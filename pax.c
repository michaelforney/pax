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
#include <fcntl.h>
#include <fnmatch.h>
#include <grp.h>
#include <pwd.h>
#include <regex.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <tar.h>
#include <unistd.h>
#ifndef makedev
#include <sys/sysmacros.h>
#endif
#include "arg.h"

#define LEN(a) (sizeof (a) / sizeof *(a))
#define ROUNDUP(x, a) (((x) + ((a) - 1)) & ~((a) - 1))

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

struct header {
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
};

struct strbuf {
	char *str;
	size_t len, cap;
};

struct extheader {
	enum field fields;
	struct strbuf path;
	uid_t uid;
	gid_t gid;
	off_t size;
	struct timespec atime, mtime, ctime;
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
static struct {
	enum field delete;
	int linkdata;
	const char *listopt;
	int times;
} opt;
static const char *exthdr_name;
static const char *globexthdr_name;
static struct extheader exthdr, globexthdr;
static struct replstr *replstr;
static time_t curtime;
static char **pats;
static size_t patslen;
static bool *patsused;
static int dest = AT_FDCWD;

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
		if (b->len)
			memcpy(s, b->str, b->len);
		free(b->str);
		if (!s)
			fatal(NULL);
		b->str = s;
	}
	return b->str + b->len;
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
copyblock(char *b, FILE *r, size_t nr, FILE *w, size_t nw)
{
	assert(nw <= nr);
	if (fread(b, 1, nr, r) != nr) {
		if (ferror(r))
			fatal("read:");
		fatal("archive truncated");
	}
	if (fwrite(b, 1, nw, w) != nw)
		fatal("write:");
}

/* nr and nw must differ by at most 8192 */
static void
copy(FILE *r, off_t nr, FILE *w, off_t nw)
{
	char b[8192];

	assert(nr - nw <= sizeof b || nw - nr <= sizeof b);
	for (; nr > sizeof b && nw > sizeof b; nr -= sizeof b, nw -= sizeof b)
		copyblock(b, r, sizeof b, w, sizeof b);
	copyblock(b, r, nr, w, nw);
}

static void
skip(FILE *f, off_t n)
{
	static bool seekfail;
	char b[8192];

	if (n == 0)
		return;
	if (!seekfail) {
		if (fseeko(f, n, SEEK_CUR) == 0)
			return;
		seekfail = true;
	}
	for (; n > sizeof b; n -= sizeof b)
		copyblock(b, f, sizeof b, NULL, 0);
	copyblock(b, f, n, NULL, 0);
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
repl(struct replstr *r, struct strbuf *b, const char *old, size_t oldlen)
{
	regmatch_t match[10];
	size_t i, n, l;
	const char *s;
	char *d;
	int flags = 0;

	b->len = 0;
	while (oldlen > 0 && regexec(&r->old, old, LEN(match), match, flags) == 0) {
		n = match[0].rm_so + (oldlen - match[0].rm_eo);
		for (s = r->new; *s; ++s) {
			i = -1;
			switch (*s) {
			case '&':  i = 0; break;
			case '\\': i = (unsigned char)*++s - '0'; break;
			}
			n += i <= 9 ? match[i].rm_eo - match[i].rm_so : 1;
		}
		d = sbufalloc(b, n + 1, 1024);
		b->len += n;
		memcpy(d, old, match[0].rm_so);
		d += match[0].rm_so;
		for (s = r->new; *s; ++s) {
			i = -1;
			switch (*s) {
			case '&':  i = 0; break;
			case '\\': i = (unsigned char)*++s - '0'; break;
			}
			if (i <= 9) {
				l = match[i].rm_eo - match[i].rm_so;
				memcpy(d, old + match[i].rm_so, l);
				d += l;
			} else {
				*d++ = *s;
			}
		}
		memcpy(d, old + match[0].rm_eo, oldlen - match[0].rm_eo);
		old += match[0].rm_eo;
		oldlen -= match[0].rm_eo;
		flags |= REG_NOTBOL;
		if (!r->global)
			break;
	}
	if (!flags)
		return 0;
	b->str[b->len] = 0;
	return 1;
}

static int
match(struct header *h)
{
	static struct {
		char *name;
		size_t namelen;
	} *dirs, *d;
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

static int
readustar(FILE *f, struct header *h)
{
	static char buf[512];
	size_t namelen, prefixlen, linklen;
	unsigned long chksum;
	size_t i;

	if (fread(buf, 1, sizeof buf, f) != sizeof buf) {
		if (ferror(f))
			fatal("read:");
		fatal("archive truncated");
	}
	chksum = 0;
	for (i = 0; i < 512; ++i)
		chksum += buf[i];
	if (chksum == 0)
		return 0;
	for (i = 148; i < 156; ++i)
		chksum += ' ' - buf[i];
	if (chksum != octnum(buf + 148, 8))
		fatal("bad checksum");
	if (memcmp(buf + 257, "ustar\0" "00", 8) != 0)
		fatal("bad magic");
	if (exthdr.fields & PATH) {
		h->name = exthdr.path.str;
		h->namelen = exthdr.path.len;
	} else if (globexthdr.fields & PATH) {
		h->name = globexthdr.path.str;
		h->namelen = globexthdr.path.len;
	} else {
		namelen = strnlen(buf, 100);
		prefixlen = strnlen(buf + 345, 155);
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
	}

	h->mode = octnum(buf + 100, 8);
	h->uid = exthdr.fields & UID ? exthdr.uid :
	         globexthdr.fields & UID ? globexthdr.uid :
	         octnum(buf + 108, 8);
	h->gid = exthdr.fields & GID ? exthdr.gid :
	         globexthdr.fields & GID ? globexthdr.gid :
	         octnum(buf + 116, 8);
	h->size = exthdr.fields & SIZE ? exthdr.size :
	          globexthdr.fields & SIZE ? globexthdr.size :
	          octnum(buf + 124, 12);
	h->mtime = exthdr.fields & MTIME ? exthdr.mtime :
	           globexthdr.fields & MTIME ? globexthdr.mtime :
	           (struct timespec){.tv_sec = octnum(buf + 136, 12)};
	h->type = buf[156];
	if (h->type == AREGTYPE)
		h->type = REGTYPE;
	
	if (exthdr.fields & LINKPATH) {
		h->link = exthdr.linkpath.str;
		h->linklen = exthdr.linkpath.len;
	} else if (globexthdr.fields & LINKPATH) {
		h->link = globexthdr.linkpath.str;
		h->linklen = globexthdr.linkpath.len;
	} else {
		linklen = strnlen(buf + 157, 100);
		if (linklen == 100) {
			h->link = malloc(linklen + 1);
			if (!h->link)
				fatal(NULL);
			memcpy(h->link, buf + 157, linklen);
			h->link[linklen] = '\0';
		} else {
			h->link = buf + 157;
		}
		h->linklen = linklen;
	}
	if (exthdr.fields & UNAME) {
		h->uname = exthdr.uname.str;
	} else if (globexthdr.fields & UNAME) {
		h->uname = globexthdr.uname.str;
	} else {
		h->uname = buf + 265;
		if (!memchr(h->uname, '\0', 32))
			fatal("uname is not NUL-terminated");
	}
	if (exthdr.fields & GNAME) {
		h->gname = exthdr.gname.str;
	} else if (globexthdr.fields & GNAME) {
		h->gname = globexthdr.gname.str;
	} else {
		h->gname = buf + 297;
		if (!memchr(h->gname, '\0', 32))
			fatal("gname is not NUL-terminated");
	}
	if (h->type == CHRTYPE || h->type == BLKTYPE) {
		unsigned major, minor;

		major = octnum(buf + 329, 8);
		minor = octnum(buf + 337, 8);
		h->dev = makedev(major, minor);
	}

	for (struct replstr *r = replstr; r; r = r->next) {
		static struct strbuf namebuf, linkbuf;

		if (repl(r, &namebuf, h->name, h->namelen)) {
			if (r->print)
				fprintf(stderr, "%s >> %s\n", h->name, namebuf.str);
			h->name = namebuf.str;
			h->namelen = namebuf.len;
			break;
		}
		if (h->type != LNKTYPE && (h->type != SYMTYPE || !r->symlink))
			continue;
		if (repl(r, &linkbuf, h->link, h->linklen)) {
			if (r->print)
				fprintf(stderr, "%s >> %s\n", h->link, linkbuf.str);
			h->link = linkbuf.str;
			h->linklen = linkbuf.len;
			break;
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
extkeyval(struct extheader *h, const char *key, const char *val, size_t vallen)
{
	char *end;

	if (strcmp(key, "atime") == 0) {
		parsetime(&h->atime, "atime", val, vallen);
		h->fields |= ATIME;
	} else if (strcmp(key, "charset") == 0) {
	} else if (strcmp(key, "comment") == 0) {
		/* ignore */
	} else if (strcmp(key, "ctime") == 0) {
		parsetime(&h->ctime, "ctime", val, vallen);
		h->fields |= CTIME;
	} else if (strcmp(key, "gid") == 0) {
		h->gid = decnum(val, vallen, &end);
		if (end != val + vallen)
			fatal("invalid extnded header: bad gid");
		h->fields |= GID;
	} else if (strcmp(key, "gname") == 0) {
		h->gname.len = 0;
		sbufcat(&h->gname, val, vallen, 256);
		h->fields |= GNAME;
	} else if (strcmp(key, "hdrcharset") == 0) {
	} else if (strcmp(key, "linkpath") == 0) {
		h->linkpath.len = 0;
		sbufcat(&h->linkpath, val, vallen, 1024);
		h->fields |= LINKPATH;
	} else if (strcmp(key, "mtime") == 0) {
		parsetime(&h->mtime, "mtime", val, vallen);
	} else if (strcmp(key, "path") == 0) {
		h->path.len = 0;
		sbufcat(&h->path, val, vallen, 1024);
		h->fields |= PATH;
	} else if (strncmp(key, "realtime.", 9) == 0) {
	} else if (strncmp(key, "security.", 9) == 0) {
	} else if (strcmp(key, "size") == 0) {
		h->size = decnum(val, vallen, &end);
		if (end != val + vallen)
			fatal("invalid extended header: bad size");
		h->fields |= SIZE;
	} else if (strcmp(key, "uid") == 0) {
		h->uid = decnum(val, vallen, &end);
		if (end != val + vallen)
			fatal("invalid extnded header: bad uid");
		h->fields |= UID;
	} else if (strcmp(key, "uname") == 0) {
		h->uname.len = 0;
		sbufcat(&h->uname, val, vallen, 256);
		h->fields |= UNAME;
	} else {
		fprintf(stderr, "ignoring unknown keyword '%s'\n", key);
	}
}

static void
readexthdr(FILE *f, struct extheader *h, off_t len)
{
	static struct strbuf buf;
	size_t reclen, vallen, padlen;
	char *rec, *end, *key, *val;

	if (len > SIZE_MAX)
		fatal("extended header is too large");
	buf.len = 0;
	sbufalloc(&buf, len, 8192);
	padlen = ROUNDUP(len, 512);
	if (fread(buf.str, 1, padlen, stdin) != padlen) {
		if (ferror(f))
			fatal("read:");
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
		extkeyval(h, key, val, vallen);
		len -= reclen;
		rec += reclen;
	}
}

static void
readgnuhdr(FILE *f, struct strbuf *b, off_t len)
{
	size_t padlen;

	if (len > SIZE_MAX - 1)
		fatal("GNU header is too large");
	b->len = 0;
	sbufalloc(b, len + 1, 1024);
	padlen = ROUNDUP(len, 512);
	if (fread(b->str, 1, padlen, f) != padlen)
		fatal("read:");
	b->str[len] = '\0';
	b->len = len;
}

static int
readpax(FILE *f, struct header *h)
{
	exthdr.fields = 0;
	while (readustar(f, h)) {
		switch (h->type) {
		case 'g': readexthdr(f, &globexthdr, h->size); break;
		case 'x': readexthdr(f, &exthdr, h->size);     break;
		case 'L': readgnuhdr(f, &exthdr.path, h->size),     exthdr.fields |= PATH;     break;
		case 'K': readgnuhdr(f, &exthdr.linkpath, h->size), exthdr.fields |= LINKPATH; break;
		default:
			if (!match(h)) {
				skip(f, ROUNDUP(h->size, 512));
				exthdr.fields = 0;
				break;
			}
			return 1;
		}
	}
	return 0;
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
	char *key, *val;
	int ext;

	for (;;) {
		s += strspn(s, " \t\n\v\f\r");
		key = s;
		if (key[0] == '\0')
			break;
		s = strchr(s, ',');
		if (s) {
			if (s > key && s[-1] == '\\')
				fatal("escaped backslashes are not yet supported");
			*s++ = '\0';
		}
		val = strchr(key, '=');
		if (key == val)
			fatal("invalid option: missing keyword");
		if (val) {
			if (val[-1] == ':') {
				ext = 1;
				val[-1] = '\0';
			} else {
				val[0] = '\0';
			}
			++val;
		}
		if (strcmp(key, "delete") == 0) {
			static const struct {
				const char *name;
				enum field field;
			} kw[] = {
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
			size_t i;

			for (i = 0; i < LEN(kw); ++i) {
				switch (fnmatch(val, kw[i].name, 0)) {
				case 0:
					opt.delete |= kw[i].field;
					break;
				case FNM_NOMATCH:
					break;
				default:
					fatal("fnmatch error");
				}
			}
		} else if (strcmp(key, "exthdr.name") == 0) {
			exthdr_name = val;
		} else if (strcmp(key, "globexthdr.name") == 0) {
			globexthdr_name = val;
		} else if (strcmp(key, "invalid") == 0) {
			fatal("option 'invalid' not implemented");
		} else if (strcmp(key, "linkdata") == 0) {
			if (val)
				fatal("option 'linkdata' should not have a value");
			opt.linkdata = 1;
		} else if (strcmp(key, "listopt") == 0) {
			opt.listopt = val;
		} else if (strcmp(key, "times") == 0) {
			if (val)
				fatal("option 'times' should not have a value");
			opt.times = 1;
		} else {
			(void)ext;
			/* XXX: need to handle := */
			extkeyval(&globexthdr, key, val, s - val);
		}
	}
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

static void
list(struct header *h)
{
	char mode[11], time[13], info[23];
	char unamebuf[(sizeof(uid_t) * CHAR_BIT + 2) / 3 + 1];
	char gnamebuf[(sizeof(gid_t) * CHAR_BIT + 2) / 3 + 1];
	const char *uname, *gname, *timefmt;
	struct tm *tm;

	skip(stdin, ROUNDUP(h->size, 512));
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
	timefmt = h->mtime.tv_sec + 157800000 < curtime ? "%b %e  %Y" : "%b %e %H:%M";
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
extract(struct header *h)
{
	FILE *f;
	int fd, retry;
	mode_t mode;

	if (vflag)
		fprintf(stderr, "%s\n", h->name);
	retry = 1;
	if (0) {
	retry:
		retry = 0;
		mkdirp(h->name, h->namelen);
	}
	switch (h->type) {
	case REGTYPE:
		fd = openat(dest, h->name, O_WRONLY|O_CREAT|O_TRUNC|O_CLOEXEC, h->mode);
		if (fd < 0) {
			if (retry && errno == ENOENT)
				goto retry;
			fatal("open %s:", h->name);
		}
		f = fdopen(fd, "w");
		if (!f)
			fatal("open %s:", h->name);
		copy(stdin, ROUNDUP(h->size, 512), f, h->size);
		fclose(f);
		return;
	case LNKTYPE:
		if (linkat(dest, h->link, dest, h->name, 0) != 0) {
			if (retry && errno == ENOENT)
				goto retry;
			fatal("link %s:", h->name);
		}
		break;
	case SYMTYPE:
		if (symlinkat(h->link, dest, h->name) != 0) {
			if (retry && errno == ENOENT)
				goto retry;
			fatal("symlink %s:", h->name);
		}
		break;
	case CHRTYPE:
	case BLKTYPE:
		mode = (h->type == CHRTYPE ? S_IFCHR : S_IFBLK) | h->mode;
		if (mknodat(dest, h->name, mode, h->dev) != 0) {
			if (retry && errno == ENOENT)
				goto retry;
			fatal("mknod %s:", h->name);
		}
		break;
	case DIRTYPE:
		if (mkdirat(dest, h->name, h->mode) != 0) {
			if (retry && errno == ENOENT)
				goto retry;
			fatal("mkdir %s:", h->name);
		}
		break;
	case FIFOTYPE:
		if (mkfifoat(dest, h->name, h->mode) != 0) {
			if (retry && errno == ENOENT)
				goto retry;
			fatal("mkfifo %s:", h->name);
		}
		break;
	}
	skip(stdin, ROUNDUP(h->size, 512));
}

int
main(int argc, char *argv[])
{
	const char *name = NULL, *arg;
	enum mode mode = LIST;
	struct header hdr;
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
		EARGF(usage());
		break;
	case 'X':
		Xflag = 1;
		break;
	default:
		usage();
	} ARGEND;

	if (name) {
		if (mode == COPY)
			usage();
		if (mode == WRITE) {
		} else if (strcmp(name, "-") != 0) {
			if (!freopen(name, "r", stdin))
				fatal("open %s:", name);
		}
	}

	curtime = time(NULL);
	if (curtime == (time_t)-1)
		fatal("time:");
	umask(0);

	pats = argv;
	patslen = argc;
	patsused = calloc(1, argc);
	if (!patsused)
		fatal(NULL);
	switch (mode) {
	case LIST:
		while (readpax(stdin, &hdr))
			list(&hdr);
		break;
	case READ:
		while (readpax(stdin, &hdr))
			extract(&hdr);
		break;
	case WRITE:
		break;
	case COPY:
		break;
	}
	for (i = 0; i < patslen; ++i) {
		if (!patsused[i])
			fatal("pattern not matched: %s", pats[i]);
	}
}
