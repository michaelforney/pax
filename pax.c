#define _XOPEN_SOURCE 700
#include <assert.h>
#include <errno.h>
#include <limits.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <dirent.h>
#include <fcntl.h>
#include <fnmatch.h>
#include <grp.h>
#include <pwd.h>
#include <regex.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/uio.h>
#include <tar.h>
#include <unistd.h>
#ifndef makedev
#include <sys/sysmacros.h>
#endif
#include "arg.h"

#define LEN(a) (sizeof (a) / sizeof *(a))
#define ROUNDUP(x, a) (((x) + ((a) - 1)) & ~((a) - 1))
#define MAXTIME 077777777777
#define MAXSIZE 077777777777
#define MAXUGID 07777777

enum mode {
	LIST,
	READ,
	WRITE,
	COPY,
};

enum format {
	CPIO,
	PAX,
	USTAR,
	GNUTAR,
	V7,
};

enum field {
	ATIME    = 1<<0,
	CTIME    = 1<<1,
	GID      = 1<<2,
	GNAME    = 1<<3,
	LINKPATH = 1<<4,
	MODE     = 1<<5,
	MTIME    = 1<<6,
	PATH     = 1<<7,
	SIZE     = 1<<8,
	UID      = 1<<9,
	UNAME    = 1<<10,
};

struct keyword {
	const char *name;
	enum field field;
};

struct header {
	/* keywords present in this header */
	enum field fields;
	/* keywords ignored because they were overridden by an option */
	enum field delete;

	char *name;
	size_t namelen;
	mode_t mode;
	uid_t uid;
	gid_t gid;
	off_t size;
	struct timespec atime, mtime, ctime;
	char type;
	char *link;
	size_t linklen;
	char *uname;
	char *gname;
	dev_t dev;

	/* tar-specific, pre-calculated split point between name and prefix */
	char *slash;
	/* read this data instead of stdin */
	char *data;
	/* source file path and flags for hard link (-l flag) */
	char *file;
	int flag;
};

struct bufio {
	int fd, err;
	off_t off;
	char buf[64 * 1024];
	char *pos, *end;
};

struct strbuf {
	char *str;
	size_t len, cap;
};

struct exthdrbuf {
	struct strbuf path;
	struct strbuf linkpath;
	struct strbuf uname;
	struct strbuf gname;
};

struct replstr {
	regex_t old;
	char *new;
	bool global;
	bool print;
	bool symlink;
	struct replstr *next;
};

struct file {
	size_t namelen;
	size_t pathlen;
	dev_t dev;
	struct file *next;
	char name[];
};

struct filelist {
	FILE *input;
	struct file *pending;
};

static int exitstatus;
static int aflag;
static int cflag;
static int dflag;
static int kflag;
static int lflag;
static int nflag;
static int tflag;
static int uflag;
static int vflag;
static int Xflag;
static int follow;
static int preserve = ATIME | MTIME;
static const struct keyword keywords[] = {
	{"atime", ATIME},
	{"gid", GID},
	{"gname", GNAME},
	{"linkpath", LINKPATH},
	{"mtime", MTIME},
	{"path", PATH},
	{"size", SIZE},
	{"uid", UID},
	{"uname", UNAME},
};
static struct {
	enum field delete;
	int linkdata;
	const char *listopt;
	const char *exthdrname;
	const char *globexthdrname;
	int times;
} opt;
static struct header exthdr, globexthdr;
static struct exthdrbuf exthdrbuf, globexthdrbuf;
static struct replstr *replstr;
static time_t curtime;
static char **pats;
static size_t patslen;
static bool *patsused;
static struct filelist files;
static struct bufio bioin;
static char *dest = "";
static int destfd = AT_FDCWD;

static void
fatal(const char *fmt, ...)
{
	va_list ap;

	if (fmt) {
		va_start(ap, fmt);
		vfprintf(stderr, fmt, ap);
		va_end(ap);
		if (fmt[0] && fmt[strlen(fmt) - 1] == ':') {
			fputc(' ', stderr);
			perror(NULL);
		} else {
			fputc('\n', stderr);
		}
	} else {
		perror(NULL);
	}
	exit(1);
}

static void *
reallocarray(void *p, size_t n, size_t m)
{
	if (m && n > SIZE_MAX / m) {
		errno = ENOMEM;
		return NULL;
	}
	return realloc(p, n * m);
}

static char *
sbufalloc(struct strbuf *b, size_t n, size_t a)
{
	char *s;

	if (n > b->cap - b->len) {
		if (n > SIZE_MAX - a || n + a > SIZE_MAX - b->len)
			fatal("path is too long");
		b->cap = ROUNDUP(n, a);
		s = malloc(b->cap);
		if (!s)
			fatal(NULL);
		if (b->len)
			memcpy(s, b->str, b->len);
		free(b->str);
		b->str = s;
	}
	return b->str + b->len;
}

static int
sbuffmtv(struct strbuf *b, size_t a, const char *fmt, va_list ap)
{
	va_list aptmp;
	int n;

	va_copy(aptmp, ap);
	n = vsnprintf(b->str ? b->str + b->len : NULL, b->cap - b->len, fmt, aptmp);
	va_end(aptmp);
	if (n < 0)
		fatal("vsnprintf:");
	if (n >= b->cap - b->len) {
		sbufalloc(b, n + 1, a);
		n = vsnprintf(b->str + b->len, b->cap - b->len, fmt, ap);
		if (n < 0)
			fatal("vsnprintf:");
		if (n >= b->cap - b->len)
			fatal("vsnprintf: formatted size changed");
	}
	b->len += n;
	return n;
}

static int
sbuffmt(struct strbuf *b, size_t a, const char *fmt, ...)
{
	va_list ap;
	int n;

	va_start(ap, fmt);
	n = sbuffmtv(b, a, fmt, ap);
	va_end(ap);
	return n;
}

static void
sbufcat(struct strbuf *b, const char *s, size_t n, size_t a)
{
	char *d;

	d = sbufalloc(b, n + 1, a);
	memcpy(d, s, n);
	d[n] = 0;
	b->len += n;
}

static void
bioinit(struct bufio *f, int fd)
{
	f->fd = fd;
	f->pos = f->end = f->buf;
	f->off = 0;
}

static size_t
bioread(struct bufio *f, void *p, size_t n)
{
	size_t l;
	unsigned char *d;
	struct iovec iov[2];
	ssize_t r;

	d = p;
	if (f->pos != f->end) {
		l = f->end - f->pos;
		if (n < l)
			l = n;
		memcpy(d, f->pos, l);
		f->pos += l;
		n -= l;
		d += l;
	}
	iov[1].iov_base = f->buf;
	iov[1].iov_len = sizeof f->buf;
	for (; n > 0; n -= r, d += r) {
		iov[0].iov_base = d;
		iov[0].iov_len = n;
		r = readv(f->fd, iov, 2);
		if (r < 0)
			f->err = errno;
		if (r <= 0)
			break;
		if (r >= n) {
			f->pos = f->buf;
			f->end = f->buf + (r - n);
			r = n;
		}
	}
	l = d - (unsigned char *)p;
	f->off += l;
	return l;
}

static int
bioskip(struct bufio *f, off_t n)
{
	static bool seekfail;
	size_t l;
	ssize_t r;

	if (f->pos != f->end) {
		l = f->end - f->pos;
		if (n < l) {
			f->pos += n;
			return 0;
		}
		n -= l;
		f->pos = f->end = f->buf;
	}
	if (!seekfail) {
		if (n == 0 || lseek(f->fd, n, SEEK_CUR) >= 0)
			return 0;
		seekfail = true;
	}
	for (; n > 0; n -= r) {
		l = sizeof f->buf;
		if (n < l)
			l = n;
		r = read(f->fd, f->buf, l);
		if (r <= 0)
			return -1;
	}
	return 0;
}

static void
copyblock(char *b, struct bufio *r, size_t nr, FILE *w, size_t nw)
{
	if (bioread(r, b, nr) != nr) {
		if (r->err)
			fatal("read: %s", strerror(errno));
		fatal("archive truncated");
	}
	if (nw > nr)
		memset(b + nr, 0, nw - nr);
	if (nw && fwrite(b, 1, nw, w) != nw)
		fatal("write:");
}

/* nr and nw must differ by at most 8192 */
static void
copy(struct bufio *r, off_t nr, FILE *w, off_t nw)
{
	char b[8192];

	assert(nr - nw <= sizeof b || nw - nr <= sizeof b);
	for (; nr > sizeof b && nw > sizeof b; nr -= sizeof b, nw -= sizeof b)
		copyblock(b, r, sizeof b, w, sizeof b);
	copyblock(b, r, nr, w, nw);
}

static unsigned long long
octnum(char *str, size_t len)
{
	unsigned c;
	unsigned long long n;

	n = 0;
	while (len > 0) {
		c = (unsigned char)*str;
		if (c == ' ' || c == '\0')
			break;
		c -= '0';
		if (c > 7)
			fatal("invalid ustar number field");
		n = n * 8 + c;
		++str;
		--len;
	}
	if (len == 0)
		fatal("invalid ustar number field: missing terminator");
	return n;
}

static unsigned long long
decnum(const char *str, size_t len, char **end)
{
	unsigned c;
	unsigned long long n;

	n = 0;
	while (len > 0) {
		c = (unsigned char)*str;
		c -= '0';
		if (c > 9)
			break;
		n = n * 10 + c;
		++str;
		--len;
	}
	if (end)
		*end = (char *)str;
	return n;
}

static int
readustar(struct bufio *f, struct header *h)
{
	static char buf[512];
	static off_t end;
	size_t namelen, prefixlen, linklen;
	unsigned long chksum;
	size_t i;
	enum format format;

	assert(bioin.off <= end);
	if (bioskip(f, end - bioin.off) != 0 || bioread(f, buf, sizeof buf) != sizeof buf) {
		if (f->err)
			fatal("read: %s", strerror(errno));
		fatal("archive truncated");
	}
	chksum = 0;
	for (i = 0; i < 512; ++i)
		chksum += ((unsigned char *)buf)[i];
	if (chksum == 0)
		return 0;
	for (i = 148; i < 156; ++i)
		chksum += ' ' - ((unsigned char *)buf)[i];
	if (chksum != octnum(buf + 148, 8))
		fatal("bad checksum");
	if (memcmp(buf + 257, "ustar\0" "00", 8) == 0)
		format = USTAR;
	else if (memcmp(buf + 257, "ustar  ", 8) == 0)
		format = GNUTAR;
	else
		format = V7;
	h->fields = PATH | UID | GID | SIZE;
	namelen = strnlen(buf, 100);
	prefixlen = format == USTAR ? strnlen(buf + 345, 155) : 0;
	if (namelen == 100 || prefixlen > 0) {
		static char namebuf[257];

		if (prefixlen > 0) {
			memcpy(namebuf, buf + 345, prefixlen);
			namebuf[prefixlen] = '/';
			++prefixlen;
		}
		memcpy(namebuf + prefixlen, buf, namelen);
		namebuf[prefixlen + namelen] = '\0';
		namelen += prefixlen;
		h->name = namebuf;
	} else {
		h->name = buf;
	}
	h->namelen = namelen;
	h->mode = octnum(buf + 100, 8);
	h->uid = octnum(buf + 108, 8);
	h->gid = octnum(buf + 116, 8);
	h->size = octnum(buf + 124, 12);
	end = bioin.off + ROUNDUP(h->size, 512);
	h->mtime = (struct timespec){.tv_sec = octnum(buf + 136, 12)};
	if (format == GNUTAR) {
		h->fields |= ATIME | CTIME;
		h->atime = (struct timespec){.tv_sec = octnum(buf + 345, 12)};
		h->ctime = (struct timespec){.tv_sec = octnum(buf + 357, 12)};
	}
	h->type = buf[156];
	if (h->type == AREGTYPE)
		h->type = REGTYPE;

	linklen = strnlen(buf + 157, 100);
	if (linklen > 0)
		h->fields |= LINKPATH;
	if (linklen == 100) {
		static char linkbuf[101];

		memcpy(linkbuf, buf + 157, 100);
		linkbuf[100] = '\0';
		h->link = linkbuf;
		h->linklen = linklen;
	} else {
		h->link = buf + 157;
	}
	h->linklen = linklen;
	if (format != V7) {
		h->fields |= UNAME | GNAME;
		h->uname = buf + 265;
		if (!memchr(h->uname, '\0', 32))
			fatal("uname is not NUL-terminated");
		h->gname = buf + 297;
		if (!memchr(h->gname, '\0', 32))
			fatal("gname is not NUL-terminated");
		if (h->type == CHRTYPE || h->type == BLKTYPE) {
			unsigned major, minor;

			major = octnum(buf + 329, 8);
			minor = octnum(buf + 337, 8);
			h->dev = makedev(major, minor);
		}
	}

	return 1;
}

static void
parsetime(struct timespec *ts, const char *field, const char *str, size_t len)
{
	const char *end = str + len;
	char *pos;
	unsigned long long subsec;
	size_t sublen;

	ts->tv_sec = decnum(str, len, &pos);
	if (*pos == '.') {
		str = ++pos;
		subsec = decnum(str, end - str, &pos);
		for (sublen = pos - str; sublen < 9; ++sublen)
			subsec *= 10;
		ts->tv_nsec = subsec % 1000000000;
	}
	if (pos != end)
		fatal("invalid extended header: bad %s", field);
}

static void
extkeyval(struct header *h, struct exthdrbuf *b, const char *key, const char *val, size_t vallen)
{
	enum field field;
	char *end;

	field = 0;
	for (size_t i = 0; i < LEN(keywords); ++i) {
		if (strcmp(key, keywords[i].name) == 0) {
			field = keywords[i].field;
			break;
		}
	}
	if (!field) {
		if (strcmp(key, "charset") == 0) {
		} else if (strcmp(key, "comment") == 0) {
			/* ignore */
		} else if (strcmp(key, "hdrcharset") == 0) {
		} else if (strncmp(key, "realtime.", 9) == 0) {
		} else if (strncmp(key, "security.", 9) == 0) {
		} else {
			fprintf(stderr, "ignoring unknown keyword '%s'\n", key);
		}
		return;
	}
	if ((h->delete | opt.delete) & field)
		return;

	switch (field) {
	case ATIME:
		parsetime(&h->atime, "atime", val, vallen);
		break;
	case CTIME:
		parsetime(&h->ctime, "ctime", val, vallen);
		break;
	case GID:
		h->gid = decnum(val, vallen, &end);
		if (end != val + vallen)
			fatal("invalid extended header: bad gid");
		break;
	case GNAME:
		b->gname.len = 0;
		sbufcat(&b->gname, val, vallen, 256);
		h->gname = b->gname.str;
		break;
	case LINKPATH:
		b->linkpath.len = 0;
		sbufcat(&b->linkpath, val, vallen, 1024);
		h->link = b->linkpath.str;
		h->linklen = b->linkpath.len;
		break;
	case MTIME:
		parsetime(&h->mtime, "mtime", val, vallen);
		break;
	case PATH:
		b->path.len = 0;
		sbufcat(&b->path, val, vallen, 1024);
		h->name = b->path.str;
		h->namelen = b->path.len;
		break;
	case SIZE:
		h->size = decnum(val, vallen, &end);
		if (end != val + vallen)
			fatal("invalid extended header: bad size");
		break;
	case UID:
		h->uid = decnum(val, vallen, &end);
		if (end != val + vallen)
			fatal("invalid extended header: bad uid");
		break;
	case UNAME:
		b->uname.len = 0;
		sbufcat(&b->uname, val, vallen, 256);
		h->uname = b->uname.str;
		break;
	default:
		return;
	}
	h->fields |= field;
}

static void
readexthdr(struct bufio *f, struct header *h, struct exthdrbuf *b, off_t len)
{
	static struct strbuf buf;
	size_t reclen, vallen;
	char *rec, *end, *key, *val;

	if (len > SIZE_MAX)
		fatal("extended header is too large");
	buf.len = 0;
	sbufalloc(&buf, len, 8192);
	if (bioread(f, buf.str, len) != len) {
		if (f->err)
			fatal("read: %s", strerror(errno));
		fatal("archive truncated");
	}
	rec = buf.str;
	while (len > 0) {
		end = memchr(rec, '\n', len);
		if (!end)
			fatal("invalid extended header: record is missing newline");
		*end = '\0';
		reclen = decnum(rec, end - rec, &key);
		if (*key != ' ' || reclen != end - rec + 1)
			fatal("invalid extended header: invalid record");
		++key;
		val = strchr(key, '=');
		if (!val)
			fatal("invalid extended header: record has no '='");
		*val++ = '\0';
		vallen = end - val;
		extkeyval(h, b, key, val, vallen);
		len -= reclen;
		rec += reclen;
	}
}

static void
readgnuhdr(struct bufio *f, struct strbuf *b, off_t len)
{
	if (len > SIZE_MAX - 1)
		fatal("GNU header is too large");
	b->len = 0;
	sbufalloc(b, len + 1, 1024);
	if (bioread(f, b->str, len) != len) {
		if (f->err)
			fatal("read: %s", strerror(errno));
		fatal("archive truncated");
	}
	b->str[len] = '\0';
	b->len = len;
}

static int
readpax(struct bufio *f, struct header *h)
{
	exthdr.fields = exthdr.delete;
	while (readustar(f, h)) {
		switch (h->type) {
		case 'g':
			readexthdr(f, &globexthdr, &globexthdrbuf, h->size);
			break;
		case 'x':
			readexthdr(f, &exthdr, &exthdrbuf, h->size);
			break;
		case 'L':
			if ((exthdr.delete | opt.delete) & PATH)
				break;
			readgnuhdr(f, &exthdrbuf.path, h->size);
			exthdr.name = exthdrbuf.path.str;
			exthdr.namelen = exthdrbuf.path.len;
			exthdr.fields |= PATH;
			break;
		case 'K':
			if ((exthdr.delete | opt.delete) & LINKPATH)
				break;
			readgnuhdr(f, &exthdrbuf.linkpath, h->size);
			exthdr.link = exthdrbuf.linkpath.str;
			exthdr.linklen = exthdrbuf.linkpath.len;
			exthdr.fields |= LINKPATH;
			break;
		default:
			return 1;
		}
	}
	return 0;
}

static char *
splitname(char *name, size_t namelen)
{
	char *slash;

	if (namelen > 256)
		return NULL;
	slash = memchr(name + namelen - 100, '/', 100);
	if (!slash || slash - name > 155)
		return NULL;
	return slash;
}

static void
openfile(struct header *h)
{
	int fd;

	if (h->file) {
		fd = open(h->file, O_RDONLY);
		if (fd < 0)
			fatal("open %s:", h->file);
		bioinit(&bioin, fd);
	}
}

static void
closefile(struct header *h)
{
	if (h->file) {
		if (tflag)
			futimens(bioin.fd, (struct timespec[2]){h->atime, {.tv_nsec = UTIME_OMIT}});
		close(bioin.fd);
	}
}

static void
closeustar(FILE *f)
{
	char pad[512];

	memset(pad, 0, 512);
	if (fwrite(pad, 512, 1, f) != 1)
		fatal("write:");
	if (fwrite(pad, 512, 1, f) != 1)
		fatal("write:");
}

static void
writeustar(FILE *f, struct header *h)
{
	char buf[512], *slash;
	unsigned long sum;
	int i;

	if (!h) {
		closeustar(f);
		return;
	}
	slash = h->slash;
	if (!slash && h->namelen > 100) {
		slash = splitname(h->name, h->namelen);
		if (!slash)
			fatal("file name is too long: %s\n", h->name);
	}
	if (slash) {
		*slash = '\0';
		strncpy(buf, slash + 1, 100);
		strncpy(buf + 345, h->name, 155);
	} else {
		strncpy(buf, h->name, 100);
		memset(buf + 345, 0, 155);
	}
	if (h->mode < 0 || h->mode > 07777777)
		fatal("mode is too large: %ju", (uintmax_t)h->mode);
	snprintf(buf + 100, 8, "%.7lo", (unsigned long)h->mode);
	if (h->uid < 0 || h->uid > MAXUGID)
		fatal("uid is too large: %ju", (uintmax_t)h->uid);
	snprintf(buf + 108, 8, "%.7lo", (unsigned long)h->uid);
	if (h->gid < 0 || h->gid > MAXUGID)
		fatal("gid is too large: %ju", (uintmax_t)h->gid);
	snprintf(buf + 116, 8, "%.7lo", (unsigned long)h->gid);
	if (h->size < 0 || h->size > MAXSIZE)
		fatal("size is too large: %ju", (uintmax_t)h->size);
	snprintf(buf + 124, 12, "%.11llo", (unsigned long long)h->size);
	if (h->mtime.tv_sec < 0 || h->mtime.tv_sec > MAXTIME)
		fatal("mtime is too large: %ju", (uintmax_t)h->mtime.tv_sec);
	snprintf(buf + 136, 12, "%.11llo", (unsigned long long)h->mtime.tv_sec);
	memset(buf + 148, ' ', 8);
	buf[156] = h->type;
	if (h->linklen > 100)
		fatal("link name is too long: %s\n", h->link);
	strncpy(buf + 157, h->link, 100);
	memcpy(buf + 257, "ustar", 6);
	memcpy(buf + 263, "00", 2);
	if (strlen(h->uname) > 31)
		fatal("user name is too long: %s\n", h->uname);
	strncpy(buf + 265, h->uname, 32);
	if (strlen(h->gname) > 31)
		fatal("group name is too long: %s\n", h->gname);
	strncpy(buf + 297, h->gname, 32);
	if (major(h->dev) > 07777777)
		fatal("device major is too large: %ju\n", (uintmax_t)major(h->dev));
	snprintf(buf + 329, 8, "%.7lo", (unsigned long)major(h->dev));
	if (minor(h->dev) > 07777777)
		fatal("device minor is too large: %ju\n", (uintmax_t)minor(h->dev));
	snprintf(buf + 337, 8, "%.7lo", (unsigned long)minor(h->dev));
	memset(buf + 500, 0, 12);
	sum = 0;
	for (i = 0; i < 512; ++i)
		sum += ((unsigned char *)buf)[i];
	snprintf(buf + 148, 8, "%.7lo", sum);
	if (fwrite(buf, 512, 1, f) != 1)
		fatal("write:");
	if (h->data) {
		size_t pad;

		if (fwrite(h->data, 1, h->size, f) != h->size)
			fatal("write:");
		pad = ROUNDUP(h->size, 512) - h->size;
		memset(bioin.buf, 0, pad);
		if (fwrite(bioin.buf, 1, pad, f) != pad)
			fatal("write:");
	} else {
		openfile(h);
		copy(&bioin, h->size, f, ROUNDUP(h->size, 512));
		closefile(h);
	}
}

static void
writerec(struct strbuf *ext, const char *fmt, ...)
{
	static struct strbuf buf;
	va_list ap;
	int d, n, m, l;

	buf.len = 0;
	va_start(ap, fmt);
	l = sbuffmtv(&buf, 256, fmt, ap);
	va_end(ap);

	d = 0;
	m = 1;
	for (n = l; n > 0; n /= 10) {
		m *= 10;
		++d;
	}
	n = d + 1 + l + 1;
	if (n >= m)
		++n;
	sbuffmt(ext, 256, "%d %.*s\n", n, l, buf.str);
}

static void
writetimerec(struct strbuf *ext, char *kw, struct timespec *ts)
{
	if (ts->tv_nsec != 0)
		writerec(ext, "%s=%ju.%.9ld", kw, (uintmax_t)ts->tv_sec, ts->tv_nsec % 1000000000);
	else
		writerec(ext, "%s=%ju", kw, (uintmax_t)ts->tv_sec);
}

static void
writeexthdr(FILE *f, int type, struct header *h)
{
	static struct strbuf ext;
	struct header exthdr;

	ext.len = 0;
	if (h->fields & PATH)
		writerec(&ext, "path=%s", h->name);
	if (h->fields & UID)
		writerec(&ext, "uid=%ju", (uintmax_t)h->uid);
	if (h->fields & GID)
		writerec(&ext, "gid=%ju", (uintmax_t)h->gid);
	if (h->fields & SIZE)
		writerec(&ext, "size=%ju", (uintmax_t)h->size);
	if (h->fields & MTIME)
		writetimerec(&ext, "mtime", &h->mtime);
	if (h->fields & ATIME)
		writetimerec(&ext, "atime", &h->atime);
	if (h->fields & CTIME)
		writetimerec(&ext, "ctime", &h->ctime);
	if (h->fields & UNAME)
		writerec(&ext, "uname=%s", h->uname);
	if (h->fields & GNAME)
		writerec(&ext, "gname=%s", h->gname);
	if (ext.len > 0) {
		memset(&exthdr, 0, sizeof exthdr);
		exthdr.name = "pax_extended_header";
		exthdr.namelen = 20;
		exthdr.mode = 0600;
		exthdr.link = "";
		exthdr.uname = "";
		exthdr.gname = "";
		exthdr.size = ext.len;
		exthdr.type = type;
		exthdr.data = ext.str;
		writeustar(f, &exthdr);
	}
}

static void
mergehdr(struct header *dst, struct header *src, enum field fields)
{
	fields &= src->fields;
	if (fields & PATH) {
		dst->name = src->name;
		dst->namelen = src->namelen;
	}
	if (fields & UID)
		dst->uid = src->uid;
	if (fields & GID)
		dst->gid = src->gid;
	if (fields & SIZE)
		dst->size = src->size;
	if (fields & MTIME)
		dst->mtime = src->mtime;
	if (fields & ATIME)
		dst->atime = src->atime;
	if (fields & CTIME)
		dst->ctime = src->ctime;
	if (fields & UNAME)
		dst->uname = src->uname;
	if (fields & GNAME)
		dst->gname = src->gname;
	if (fields & LINKPATH) {
		dst->link = src->link;
		dst->linklen = src->linklen;
	}
	dst->fields |= fields;
}

static void
writepax(FILE *f, struct header *h)
{
	enum field fields;

	if (!h) {
		closeustar(f);
		return;
	}
	if (vflag)
		fprintf(stderr, "%s\n", h->name);
	fields = 0;
	if (h->namelen > 100) {
		h->slash = splitname(h->name, h->namelen);
		if (!h->slash)
			fields |= PATH;
	}
	if (h->uid > MAXUGID)
		fields |= UID;
	if (h->gid > MAXUGID)
		fields |= GID;
	if (h->size > MAXSIZE)
		fields |= SIZE;
	if (h->mtime.tv_sec > MAXTIME || h->mtime.tv_nsec != 0)
		fields |= MTIME;
	if (opt.times) {
		fields |= ATIME;
		fields |= CTIME;
	}
	if (strlen(h->uname) > 31)
		fields |= UNAME;
	if (strlen(h->gname) > 31)
		fields |= GNAME;
	if (h->linklen > 100)
		fields |= LINKPATH;
	fields &= ~(exthdr.fields | opt.delete);
	mergehdr(&exthdr, h, fields);
	writeexthdr(f, 'x', &exthdr);

	/* reset fields merged into extended header */
	if (fields & PATH) {
		h->name = "";
		h->namelen = 0;
	}
	if (fields & UID)
		h->uid = 0;
	if (fields & GID)
		h->gid = 0;
	if (fields & SIZE)
		h->size = 0;
	if (fields & MTIME) {
		if (h->mtime.tv_sec > MAXTIME)
			h->mtime.tv_sec = MAXTIME;
		h->mtime.tv_nsec = 0;
	}
	if (fields & ATIME) {
		if (h->atime.tv_sec > MAXTIME)
			h->atime.tv_sec = MAXTIME;
		h->atime.tv_nsec = 0;
	}
	if (fields & CTIME) {
		if (h->ctime.tv_sec > MAXTIME)
			h->ctime.tv_sec = MAXTIME;
		h->ctime.tv_nsec = 0;
	}
	if (fields & UNAME)
		h->uname = "";
	if (fields & GNAME)
		h->gname = "";
	if (fields & LINKPATH) {
		h->link = "";
		h->linklen = 0;
	}
	h->fields &= ~fields;
	writeustar(f, h);
}

static void
filepush(struct filelist *files, const char *name, size_t pathlen, dev_t dev)
{
	struct file *f;
	size_t namelen;

	namelen = strlen(name);
	f = malloc(sizeof *f + namelen + 1);
	if (!f)
		fatal(NULL);
	memcpy(f->name, name, namelen + 1);
	f->namelen = namelen;
	f->pathlen = pathlen;
	f->dev = dev;
	f->next = files->pending;
	files->pending = f;
}

static int
readfile(struct bufio *f, struct header *h)
{
	static struct strbuf name, link;
	struct stat st;
	int flag;
	DIR *dir;
	struct dirent *d;
	ssize_t ret;
	dev_t dev;

next:
	flag = follow == 'L' ? 0 : AT_SYMLINK_NOFOLLOW;
	if (files.pending) {
		struct file *f;

		f = files.pending;
		files.pending = f->next;
		assert(f->pathlen <= name.len);
		name.len = f->pathlen;
		sbufcat(&name, f->name, f->namelen, 1024);
		if (follow == 'H' && f->pathlen > 0)
			flag &= ~AT_SYMLINK_NOFOLLOW;
		dev = f->dev;
		free(f);
	} else {
		if (!files.input)
			return 0;
		ret = getline(&name.str, &name.cap, files.input);
		if (ret < 0) {
			if (ferror(files.input))
				fatal("getline:");
			return 0;
		}
		if (ret > 0 && name.str[ret - 1] == '\n')
			name.str[--ret] = '\0';
		name.len = ret;
		dev = 0;
	}

	if (fstatat(AT_FDCWD, name.str, &st, flag) != 0)
		fatal("stat %s:", name.str);
	if (Xflag && dev && st.st_dev != dev)
		goto next;
	h->fields = PATH | UID | GID | ATIME | MTIME | CTIME;
	h->name = name.str;
	h->namelen = name.len;
	h->slash = NULL;
	h->mode = st.st_mode & ~S_IFMT;
	h->uid = st.st_uid;
	h->gid = st.st_gid;
	h->size = 0;
	h->atime = st.st_atim;
	h->mtime = st.st_mtim;
	h->ctime = st.st_ctim;
	h->uname = "";
	h->gname = "";
	h->link = "";
	h->linklen = 0;
	h->dev = 0;
	h->slash = NULL;
	h->data = NULL;
	h->file = name.str;
	h->flag = flag;
	switch (st.st_mode & S_IFMT) {
	case S_IFREG:
		h->type = REGTYPE;
		h->size = st.st_size;
		break;
	case S_IFLNK:
		h->type = SYMTYPE;
		link.len = 0;
		sbufalloc(&link, 1024, 1024);
		for (;;) {
			ret = readlink(name.str, link.str, link.cap - 1);
			if (ret < 0)
				fatal("readlink %s:", name.str);
			if (ret < link.cap)
				break;
			if (link.cap > SSIZE_MAX / 2)
				fatal("symlink target is too long");
			sbufalloc(&link, link.cap * 2, 1024);
		}
		link.str[ret] = '\0';
		link.len = ret;
		h->link = link.str;
		h->linklen = link.len;
		break;
	case S_IFCHR:
		h->type = CHRTYPE;
		h->dev = st.st_rdev;
		break;
	case S_IFBLK:
		h->type = BLKTYPE;
		h->dev = st.st_rdev;
		break;
	case S_IFDIR:
		h->type = DIRTYPE;
		if (name.str[name.len - 1] != '/')
			sbufcat(&name, "/", 1, 1024);
		dir = opendir(name.str);
		if (!dir)
			fatal("opendir %s:", name.str);
		for (;;) {
			errno = 0;
			d = readdir(dir);
			if (!d)
				break;
			if (strcmp(d->d_name, ".") == 0 || strcmp(d->d_name, "..") == 0)
				continue;
			filepush(&files, d->d_name, name.len, st.st_dev);
		}
		if (errno != 0)
			fatal("readdir %s:", name.str);
		closedir(dir);
		break;
	case S_IFIFO:
		h->type = FIFOTYPE;
		break;
	}
	return 1;
}

static void
usage(void)
{
	fprintf(stderr, "usage: pax\n");
	exit(2);
}

static void
parseopts(char *s)
{
	char *key, *val, *end, *d;
	int ext;

	for (;;) {
		s += strspn(s, " \t\n\v\f\r");
		if (!*s)
			break;
		key = s;
		while (*s && *s != ',' && *s != '=')
			++s;
		val = NULL;
		if (*s == '=') {
			ext = s > key && s[-1] == ':';
			s[-ext] = '\0';
			val = ++s;
			for (d = s; *s && *s != ','; ++s, ++d) {
				if (*s == '\\')
					++s;
				if (d < s)
					*d = *s;
			}
			end = d;
		}
		if (*s == ',')
			*s++ = '\0';
		if (strcmp(key, "linkdata") == 0) {
			if (val)
				fatal("option 'linkdata' must not have a value");
			opt.linkdata = 1;
		} else if (strcmp(key, "times") == 0) {
			if (val)
				fatal("option 'times' must not have a value");
			opt.times = 1;
		} else if (!val) {
			fatal("option '%s' must have a value", key);
		} else if (strcmp(key, "delete") == 0) {
			for (size_t i = 0; i < LEN(keywords); ++i) {
				switch (fnmatch(val, keywords[i].name, 0)) {
				case 0: opt.delete |= keywords[i].field; break;
				case FNM_NOMATCH: break;
				default: fatal("fnmatch error");
				}
			}
		} else if (strcmp(key, "exthdr.name") == 0) {
			opt.exthdrname = val;
		} else if (strcmp(key, "globexthdr.name") == 0) {
			opt.globexthdrname = val;
		} else if (strcmp(key, "invalid") == 0) {
			fatal("option 'invalid' is not implemented");
		} else if (strcmp(key, "listopt") == 0) {
			opt.listopt = val;
		} else if (ext) {
			extkeyval(&exthdr, &exthdrbuf, key, val, end - val);
		} else {
			extkeyval(&globexthdr, &globexthdrbuf, key, val, end - val);
		}
	}
}

static void
listhdr(FILE *f, struct header *h)
{
	char mode[11], time[13], info[23];
	char unamebuf[(sizeof(uid_t) * CHAR_BIT + 2) / 3 + 1];
	char gnamebuf[(sizeof(gid_t) * CHAR_BIT + 2) / 3 + 1];
	const char *uname, *gname, *timefmt;
	struct tm *tm;

	if (!h)
		return;
	if (opt.listopt)
		fatal("listopt is not supported");
	if (!vflag) {
		printf("%s\n", h->name);
		return;
	}
	memset(mode, '-', sizeof mode - 1);
	mode[10] = '\0';
	switch (h->type) {
	case SYMTYPE: mode[0] = 'l'; break;
	case CHRTYPE: mode[0] = 'c'; break;
	case BLKTYPE: mode[0] = 'b'; break;
	case DIRTYPE: mode[0] = 'd'; break;
	case FIFOTYPE: mode[0] = 'p'; break;
	}
	if (h->mode & S_IRUSR) mode[1] = 'r';
	if (h->mode & S_IWUSR) mode[2] = 'w';
	if (h->mode & S_IXUSR) mode[3] = 'x';
	if (h->mode & S_IRGRP) mode[4] = 'r';
	if (h->mode & S_IWGRP) mode[5] = 'w';
	if (h->mode & S_IXGRP) mode[6] = 'x';
	if (h->mode & S_IROTH) mode[7] = 'r';
	if (h->mode & S_IWOTH) mode[8] = 'w';
	if (h->mode & S_IXOTH) mode[9] = 'x';
	if (h->mode & S_ISUID) mode[3] = mode[3] == 'x' ? 's' : 'S';
	if (h->mode & S_ISGID) mode[3] = mode[6] == 'x' ? 's' : 'S';
	if (h->mode & S_ISVTX) mode[9] = mode[9] == 'x' ? 't' : 'T';
	uname = h->uname;
	if (!uname[0]) {
		snprintf(unamebuf, sizeof unamebuf, "%ju", (uintmax_t)h->uid);
		uname = unamebuf;
	}
	gname = h->gname;
	if (!gname[0]) {
		snprintf(gnamebuf, sizeof gnamebuf, "%ju", (uintmax_t)h->gid);
		gname = gnamebuf;
	}
	timefmt = h->mtime.tv_sec + 15780000 < curtime ? "%b %e  %Y" : "%b %e %H:%M";
	tm = localtime(&h->mtime.tv_sec);
	if (!tm)
		fatal("localtime:");
	strftime(time, sizeof time, timefmt, tm);
	if (h->type == CHRTYPE || h->type == BLKTYPE)
		snprintf(info, sizeof info, "%u, %u", major(h->dev), minor(h->dev));
	else
		snprintf(info, sizeof info, "%ju", (uintmax_t)h->size);
	printf("%s %2d %-8s %-8s %9s %s %s", mode, 1, uname, gname, info, time, h->name);
	switch (h->type) {
	case LNKTYPE: printf(" == %s", h->link); break;
	case SYMTYPE: printf(" -> %s", h->link); break;
	}
	putchar('\n');
}

static void
mkdirp(char *name, size_t len)
{
	char *p;

	if (len == 0)
		return;
	for (p = name + 1; p < name + len - 1; ++p) {
		if (*p != '/')
			continue;
		*p = 0;
		if (mkdir(name, 0777) != 0 && errno != EEXIST)
			fatal("mkdir %s:", name);
		*p = '/';
	}
}

static void
writefile(FILE *unused, struct header *h)
{
	FILE *f;
	int fd, retry, flags;
	struct stat st;
	mode_t mode;

	if (!h)
		return;
	if (uflag && fstatat(destfd, h->name, &st, 0) == 0) {
		if (h->mtime.tv_sec < st.st_mtime || (h->mtime.tv_sec == st.st_mtime
		 && h->mtime.tv_nsec < st.st_mtim.tv_nsec))
			return;
	}
	if (vflag)
		fprintf(stderr, "%s\n", h->name);
	if (lflag && h->file && h->type != DIRTYPE) {
		if (linkat(AT_FDCWD, h->file, destfd, h->name, h->flag) == 0)
			return;
	}
	retry = 1;
	if (0) {
	retry:
		retry = 0;
		mkdirp(h->name, h->namelen);
	}
	mode = h->mode & ~(S_ISUID | S_ISGID);
	switch (h->type) {
	case REGTYPE:
		flags = O_WRONLY|O_CREAT|O_TRUNC|O_CLOEXEC;
		if (kflag)
			flags |= O_EXCL;
		fd = openat(destfd, h->name, flags, mode);
		if (fd < 0) {
			if (retry && errno == ENOENT)
				goto retry;
			fatal("open %s%s:", dest, h->name);
		}
		f = fdopen(fd, "w");
		if (!f)
			fatal("open %s:", h->name);
		openfile(h);
		copy(&bioin, h->size, f, h->size);
		closefile(h);
		fclose(f);
		break;
	case LNKTYPE:
		if (linkat(destfd, h->link, destfd, h->name, 0) != 0) {
			if (retry && errno == ENOENT)
				goto retry;
			fatal("link %s%s:", dest, h->name);
		}
		break;
	case SYMTYPE:
		if (symlinkat(h->link, destfd, h->name) != 0) {
			if (retry && errno == ENOENT)
				goto retry;
			fatal("symlink %s%s:", dest, h->name);
		}
		break;
	case CHRTYPE:
	case BLKTYPE:
		mode |= h->type == CHRTYPE ? S_IFCHR : S_IFBLK;
		if (mknodat(destfd, h->name, mode, h->dev) != 0) {
			if (retry && errno == ENOENT)
				goto retry;
			fatal("mknod %s%s:", dest, h->name);
		}
		break;
	case DIRTYPE:
		if (mkdirat(destfd, h->name, mode) != 0) {
			if (retry && errno == ENOENT)
				goto retry;
			if (errno == EEXIST) {
				if (fstatat(destfd, h->name, &st, 0) == 0 && S_ISDIR(st.st_mode))
					break;
				errno = EEXIST;
			}
			fatal("mkdir %s%s:", dest, h->name);
		}
		break;
	case FIFOTYPE:
		if (mkfifoat(destfd, h->name, mode) != 0) {
			if (retry && errno == ENOENT)
				goto retry;
			if (errno == EEXIST) {
				if (fstatat(destfd, h->name, &st, 0) == 0 && S_ISFIFO(st.st_mode))
					break;
				errno = EEXIST;
			}
			fatal("mkfifo %s%s:", dest, h->name);
		}
		break;
	}
	if (preserve & (ATIME | MTIME)) {
		struct timespec ts[2];

		ts[0] = preserve & ATIME ? h->atime : (struct timespec){.tv_nsec = UTIME_OMIT};
		ts[1] = preserve & MTIME ? h->mtime : (struct timespec){.tv_nsec = UTIME_OMIT};
		if (utimensat(destfd, h->name, ts, 0) != 0) {
			fprintf(stderr, "utimens %s%s: %s\n", dest, h->name, strerror(errno));
			exitstatus = 1;
		}
	}
	if (preserve & (UID | GID)) {
		uid_t uid;
		gid_t gid;

		uid = preserve & UID ? h->uid : -1;
		gid = preserve & UID ? h->uid : -1;
		if (fchownat(destfd, h->name, uid, gid, 0) != 0) {
			fprintf(stderr, "chown %s%s: %s\n", dest, h->name, strerror(errno));
			exitstatus = 1;
		}
		/* add back setuid/setgid bits if we preserved the uid/gid */
		mode = h->mode;
	}
	if (preserve & MODE) {
		if (fchmodat(destfd, h->name, mode, 0) != 0) {
			fprintf(stderr, "chmod %s%s: %s\n", dest, h->name, strerror(errno));
			exitstatus = 1;
		}
	}
}

static int
match(struct header *h)
{
	static struct dir {
		char *name;
		size_t namelen;
	} *dirs;
	static size_t dirslen;
	size_t i;

	if (patslen == 0)
		return 1;
	if (!dflag) {
		for (i = 0; i < dirslen; ++i) {
			if (h->namelen >= dirs[i].namelen && memcmp(h->name, dirs[i].name, dirs[i].namelen) == 0)
				return !cflag;
		}
	}
	for (i = 0; i < patslen; ++i) {
		if (nflag && patsused[i])
			continue;
		switch (fnmatch(pats[i], h->name, FNM_PATHNAME | FNM_PERIOD)) {
		case 0:
			patsused[i] = 1;
			if (!dflag && h->type == DIRTYPE) {
				struct dir *d;

				if ((dirslen & (dirslen - 1)) == 0) {
					dirs = reallocarray(dirs, dirslen ? dirslen * 2 : 32, sizeof *dirs);
					if (!dirs)
						fatal(NULL);
				}
				d = &dirs[dirslen++];
				d->namelen = h->namelen;
				d->name = malloc(d->namelen + 1);
				if (!d->name)
					fatal(NULL);
				memcpy(d->name, h->name, h->namelen);
				/* add trailing slash if not already present */
				if (d->name[d->namelen - 1] != '/')
					d->name[d->namelen++] = '/';
			}
			return !cflag;
		case FNM_NOMATCH:
			break;
		default:
			fatal("fnmatch error");
		}
	}
	return cflag;
}

static void
parsereplstr(char *str)
{
	static struct replstr **end = &replstr;
	struct replstr *r;
	char *old, *new, delim;
	int err;

	delim = str[0];
	if (!delim)
		usage();
	old = str + 1;
	str = strchr(old, delim);
	if (!str)
		usage();
	*str = 0;
	new = str + 1;
	str = strchr(new, delim);
	if (!str)
		usage();
	*str = 0;

	r = malloc(sizeof *r);
	if (!r)
		fatal(NULL);
	r->next = NULL;
	r->global = false;
	r->print = false;
	r->symlink = false;
	for (;;) {
		switch (*++str) {
		case 'g': r->global = true; break;
		case 'p': r->print = true; break;
		case 's': r->symlink = false; break;
		case 'S': r->symlink = true; break;
		case 0: goto done;
		}
	}
done:
	err = regcomp(&r->old, old, REG_NEWLINE);
	if (err != 0) {
		char errbuf[256];

		regerror(err, &r->old, errbuf, sizeof errbuf);
		fatal("invalid regular expression: %s", errbuf);
	}
	r->new = new;
	*end = r;
	end = &r->next;
}

static int
applyrepl(struct replstr *r, struct strbuf *b, const char *old, size_t oldlen)
{
	regmatch_t match[10];
	size_t i, n, l;
	const char *s, *p;
	char *d;
	int flags;

	flags = 0;
	b->len = 0;
	p = old;
	while (regexec(&r->old, p, LEN(match), match, flags) == 0) {
		n = match[0].rm_so;
		for (s = r->new; *s; ++s) {
			switch (*s) {
			case '&':  i = 0; break;
			case '\\': i = *++s - '0'; break;
			default:   i = -1; break;
			}
			n += i <= 9 ? match[i].rm_eo - match[i].rm_so : 1;
		}
		d = sbufalloc(b, n + 1, 1024);
		b->len += n;
		memcpy(d, p, match[0].rm_so);
		d += match[0].rm_so;
		for (s = r->new; *s; ++s) {
			switch (*s) {
			case '&':  i = 0; break;
			case '\\': i = *++s - '0'; break;
			default:   i = -1; break;
			}
			if (i <= 9) {
				l = match[i].rm_eo - match[i].rm_so;
				memcpy(d, p + match[i].rm_so, l);
				d += l;
			} else {
				*d++ = *s;
			}
		}
		flags |= REG_NOTBOL;
		p += match[0].rm_eo;
		if (!r->global)
			break;
	}
	if (p == old)
		return 0;
	sbufcat(b, p, oldlen - (p - old), 1024);
	if (r->print)
		fprintf(stderr, "%s >> %s\n", old, b->str);
	return 1;
}

static void
replace(struct header *h)
{
	struct replstr *r;

	for (r = replstr; r; r = r->next) {
		if (applyrepl(r, &exthdrbuf.path, h->name, h->namelen)) {
			h->name = exthdrbuf.path.str;
			h->namelen = exthdrbuf.path.len;
			break;
		}
	}
	if (h->type != LNKTYPE && h->type != SYMTYPE)
		return;
	for (r = replstr; r; r = r->next) {
		if (h->type == SYMTYPE && !r->symlink)
			continue;
		if (applyrepl(r, &exthdrbuf.linkpath, h->link, h->linklen)) {
			h->link = exthdrbuf.linkpath.str;
			h->linklen = exthdrbuf.linkpath.len;
			break;
		}
	}
}

int
main(int argc, char *argv[])
{
	const char *name = NULL, *arg, *format = "pax";
	enum mode mode = LIST;
	struct header hdr;
	int (*readhdr)(struct bufio *, struct header *) = readpax;
	void (*writehdr)(FILE *, struct header *) = listhdr;
	size_t i;

	ARGBEGIN {
	case 'a':
		aflag = 1;
		break;
	case 'b':
		EARGF(usage());
		break;
	case 'c':
		cflag = 1;
		break;
	case 'd':
		dflag = 1;
		break;
	case 'f':
		name = EARGF(usage());
		break;
	case 'H':
		follow = 'H';
		break;
	case 'k':
		kflag = 1;
		break;
	case 'l':
		lflag = 1;
		break;
	case 'L':
		follow = 'L';
		break;
	case 'n':
		nflag = 1;
		break;
	case 'o':
		parseopts(EARGF(usage()));
		break;
	case 'p':
		for (arg = EARGF(usage()); *arg; ++arg) {
			switch (*arg) {
			case 'a': preserve &= ~ATIME; break;
			case 'e': preserve = ~0; break;
			case 'm': preserve &= ~MTIME; break;
			case 'o': preserve |= UID | GID; break;
			case 'p': preserve |= MODE; break;
			default: fatal("unknown -p option");
			}
		}
		break;
	case 'r':
		mode |= READ;
		break;
	case 's':
		parsereplstr(EARGF(usage()));
		break;
	case 't':
		tflag = 1;
		break;
	case 'u':
		uflag = 1;
		break;
	case 'v':
		vflag = 1;
		break;
	case 'w':
		mode |= WRITE;
		break;
	case 'x':
		format = EARGF(usage());
		break;
	case 'X':
		Xflag = 1;
		break;
	default:
		usage();
	} ARGEND;

	curtime = time(NULL);
	if (curtime == (time_t)-1)
		fatal("time:");
	exthdr.fields &= ~opt.delete;
	exthdr.delete = exthdr.fields;
	globexthdr.fields &= ~opt.delete;
	globexthdr.delete = globexthdr.fields;

	switch (mode) {
	case READ:
		writehdr = writefile;
		/* fallthrough */
	case LIST:
		if (name && strcmp(name, "-") != 0) {
			bioin.fd = open(name, O_RDONLY);
			if (bioin.fd < 0)
				fatal("open %s:", name);
		}
		pats = argv;
		patslen = argc;
		patsused = calloc(1, argc);
		if (!patsused)
			fatal(NULL);
		break;
	case WRITE:
		if (name && strcmp(name, "-") != 0 && !freopen(name, "w", stdout))
			fatal("open %s:", name);
		if (strcmp(format, "ustar") == 0) {
			writehdr = writeustar;
		} else if (strcmp(format, "pax") == 0) {
			writehdr = writepax;
			if (globexthdr.fields)
				writeexthdr(stdout, 'g', &globexthdr);
		} else {
			fatal("unsupported archive format '%s'", arg);
		}
		break;
	case COPY:
		if (name || argc == 0)
			usage();
		i = strlen(argv[--argc]);
		dest = malloc(i + 2);
		if (!dest)
			fatal(NULL);
		memcpy(dest, argv[argc], i);
		memcpy(dest + i, "/", 2);
		destfd = open(dest, O_SEARCH|O_DIRECTORY);
		if (destfd < 0)
			fatal("open %s:", dest);
		writehdr = writefile;
		break;
	}
	if (mode & WRITE) {
		readhdr = readfile;
		bioin.fd = -1;
		for (i = 0; i < argc; ++i)
			filepush(&files, argv[i], 0, 0);
		if (argc == 0)
			files.input = stdin;
	}

	while (readhdr(&bioin, &hdr)) {
		mergehdr(&hdr, &exthdr, ~0);
		mergehdr(&hdr, &globexthdr, ~exthdr.fields);
		if (match(&hdr)) {
			replace(&hdr);
			writehdr(stdout, &hdr);
		}
	}
	writehdr(stdout, NULL);
	for (i = 0; i < patslen; ++i) {
		if (!patsused[i])
			fatal("pattern not matched: %s", pats[i]);
	}

	return exitstatus;
}
