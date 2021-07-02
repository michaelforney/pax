#define _POSIX_C_SOURCE 200809L
#include <limits.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <fnmatch.h>
#include <grp.h>
#include <pwd.h>
#include <regex.h>
#include <sys/stat.h>
#include <sys/types.h>
#ifndef makedev
#include <sys/sysmacros.h>
#endif
#include "arg.h"

#define LEN(a) (sizeof(a) / sizeof((a)[0]))

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
	GID      = 1<<1,
	GNAME    = 1<<2,
	LINKPATH = 1<<3,
	MTIME    = 1<<4,
	PATH     = 1<<5,
	SIZE     = 1<<6,
	UID      = 1<<7,
	UNAME    = 1<<8,
};

struct header {
	char *name;
	mode_t mode;
	uid_t uid;
	gid_t gid;
	off_t size;
	struct timespec atime, mtime, ctime;
	char type;
	char *linkname;
	char *uname;
	char *gname;
	dev_t dev;
};

struct replstr {
	regex_t reg;
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
static struct {
	enum field delete;
	int linkdata;
	const char *listopt;
} opt;
static const char *exthdr_name;
static const char *globexthdr_name;
static struct header exthdr, globexthdr;
static time_t curtime;

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
memdup(const void *src, size_t len)
{
	void *dst;

	dst = malloc(len);
	if (dst)
		memcpy(dst, src, len);
	return dst;
}

static void
skip(FILE *f, size_t len)
{
	char buf[8192];
	size_t n = sizeof(buf);

	while (len > 0) {
		if (len < n)
			n = len;
		if (fread(buf, 1, n, f) != n) {
			if (ferror(f))
				fatal("read:");
			fatal("archive truncated");
		}
		len -= n;
	}
}

static unsigned long long
octnum(char *str, size_t len)
{
	int c;
	unsigned long long n;

	n = 0;
	while (len > 0) {
		c = (unsigned)*str;
		if (c == ' ' || c == '\0')
			break;
		if (c < '0' || c > '7')
			fatal("invalid ustar number field");
		n = n * 8 + (c - '0');
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
	int c;
	unsigned long long n;

	n = 0;
	while (len > 0) {
		c = (unsigned)*str;
		if (c < '0' || c > '9')
			break;
		n = n * 10 + (c - '0');
		++str;
		--len;
	}
	if (end)
		*end = (char *)str;
	return n;
}

static int
readustar(FILE *f, struct header *h)
{
	static char buf[512];
	size_t namelen, prefixlen, linklen;
	unsigned major, minor;
	unsigned long sum, chksum;
	int zero;
	size_t i;

	if (fread(buf, 1, sizeof(buf), f) != sizeof(buf)) {
		if (ferror(f))
			fatal("read:");
		fatal("archive truncated");
	}
	sum = 0;
	zero = 1;
	for (i = 0; i < sizeof(buf); ++i) {
		sum += (i < 148 || i > 155) ? buf[i] : ' ';
		if (buf[i])
			zero = 0;
	}
	if (zero)
		return 0;
	chksum = octnum(buf + 148, 8);
	if (sum != chksum)
		fatal("bad checksum: %lu != %lu", sum, chksum);
	if (exthdr.name) {
		h->name = exthdr.name;
	} else if (globexthdr.name) {
		h->name = globexthdr.name;
	} else {
		namelen = strnlen(buf, 100);
		prefixlen = strnlen(buf + 345, 155);
		if (namelen == 100 || prefixlen > 0) {
			h->name = malloc(namelen + prefixlen + 2);
			if (!h->name)
				fatal(NULL);
			memcpy(h->name, buf, namelen);
			h->name[namelen] = '\0';
			memcpy(h->name + namelen + 1, buf + 345, prefixlen);
			h->name[namelen + 1 + prefixlen] = '\0';
		} else {
			h->name = buf;
		}
	}

	h->mode = octnum(buf + 100, 8);
	h->uid = octnum(buf + 108, 8);
	h->gid = octnum(buf + 116, 8);
	h->size = octnum(buf + 124, 12);
	h->mtime.tv_sec = octnum(buf + 136, 12);
	h->mtime.tv_nsec = 0;
	h->type = buf[156];
	
	if (exthdr.linkname) {
		h->linkname = exthdr.linkname;
	} else if (globexthdr.linkname) {
		h->linkname = globexthdr.linkname;
	} else {
		linklen = strnlen(buf + 157, 100);
		if (linklen == 100) {
			h->linkname = malloc(linklen + 1);
			if (!h->linkname)
				fatal(NULL);
			memcpy(h->linkname, buf + 157, linklen);
			h->linkname[linklen] = '\0';
		} else {
			h->linkname = buf + 157;
		}
	}
	if (exthdr.uname) {
		h->uname = exthdr.uname;
	} else if (globexthdr.uname) {
		h->uname = globexthdr.uname;
	} else {
		h->uname = buf + 265;
		if (!memchr(h->uname, '\0', 32))
			fatal("uname is not NUL-terminated");
	}
	if (exthdr.gname) {
		h->gname = exthdr.gname;
	} else if (globexthdr.gname) {
		h->gname = globexthdr.gname;
	} else {
		h->gname = buf + 297;
		if (!memchr(h->gname, '\0', 32))
			fatal("gname is not NUL-terminated");
	}
	if (h->type == '3' || h->type == '4') {
		major = octnum(buf + 329, 8);
		minor = octnum(buf + 337, 8);
		h->dev = makedev(major, minor);
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
extkeyval(struct header *h, const char *key, const char *val, size_t vallen)
{
	char *end;

	if (strcmp(key, "atime") == 0) {
		parsetime(&h->atime, "atime", val, vallen);
	} else if (strcmp(key, "charset") == 0) {
	} else if (strcmp(key, "comment") == 0) {
		/* ignore */
	} else if (strcmp(key, "ctime") == 0) {
		parsetime(&h->ctime, "ctime", val, vallen);
	} else if (strcmp(key, "gid") == 0) {
		h->gid = strtoul(val, &end, 10);
		if (end != val + vallen)
			fatal("invalid extnded header: bad gid");
	} else if (strcmp(key, "gname") == 0) {
		h->gname = memdup(val, vallen);
		if (!h->gname)
			fatal(NULL);
	} else if (strcmp(key, "hdrcharset") == 0) {
	} else if (strcmp(key, "linkpath") == 0) {
		h->linkname = memdup(val, vallen);
		if (!h->linkname)
			fatal(NULL);
	} else if (strcmp(key, "mtime") == 0) {
		parsetime(&h->mtime, "mtime", val, vallen);
	} else if (strcmp(key, "path") == 0) {
		h->name = memdup(val, vallen);
		if (!h->name)
			fatal(NULL);
	} else if (strncmp(key, "realtime.", 9) == 0) {
	} else if (strncmp(key, "security.", 9) == 0) {
	} else if (strcmp(key, "size") == 0) {
		h->size = strtoull(val, &end, 10);
		if (end != val + vallen)
			fatal("invalid extended header: bad size");
	} else if (strcmp(key, "uid") == 0) {
		h->uid = strtoul(val, &end, 10);
		if (end != val + vallen)
			fatal("invalid extnded header: bad uid");
	} else if (strcmp(key, "uname") == 0) {
		h->uname = memdup(val, vallen);
		if (!h->uname)
			fatal(NULL);
	} else {
		fprintf(stderr, "ignoring unknown keyword '%s'\n", key);
	}
}

static void
readexthdr(FILE *f, struct header *h, size_t len)
{
	static char *buf = NULL;
	static size_t buflen = 0;
	size_t reclen, vallen, pad;
	char *rec, *end, *key, *val;

	pad = ((len + 511) & ~511);
	if (buflen < len) {
		buflen = (pad + 8191) & ~8191;
		free(buf);
		buf = malloc(buflen);
		if (!buf)
			fatal(NULL);
	}
	if (fread(buf, 1, pad, stdin) != pad) {
		if (ferror(f))
			fatal("read:");
		fatal("archive truncated");
	}
	rec = buf;
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

static int
readpax(FILE *f, struct header *h)
{
	memset(&exthdr, 0, sizeof(exthdr));
	for (;;) {
		if (readustar(f, h) == 0)
			return 0;
		switch (h->type) {
		case 'g':
			readexthdr(f, &globexthdr, h->size);
			break;
		case 'x':
			readexthdr(f, &exthdr, h->size);
			break;
		default:
			return 1;
		}
	}
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
			static struct {
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
		} else {
			(void)ext;
			/* XXX: need to handle := */
			extkeyval(&globexthdr, key, val, s - val);
		}
	}
}

static void
list(struct header *h)
{
	char mode[11], time[13], info[23];
	char unamebuf[(sizeof(uid_t) * CHAR_BIT + 2) / 3 + 1];
	char gnamebuf[(sizeof(gid_t) * CHAR_BIT + 2) / 3 + 1];
	const char *uname, *gname, *timefmt;
	struct tm *tm;

	memset(mode, '-', sizeof(mode) - 1);
	switch (h->type) {
	case '2': mode[0] = 'l'; break;
	case '3': mode[0] = 'c'; break;
	case '4': mode[0] = 'b'; break;
	case '5': mode[0] = 'd'; break;
	case '6': mode[0] = 'p'; break;
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
		snprintf(unamebuf, sizeof(unamebuf), "%ju", (uintmax_t)h->uid);
		uname = unamebuf;
	}
	gname = h->gname;
	if (!gname[0]) {
		snprintf(gnamebuf, sizeof(gnamebuf), "%ju", (uintmax_t)h->gid);
		gname = gnamebuf;
	}
	timefmt = h->mtime.tv_sec + 157800000 < curtime ? "%b %e  %Y" : "%b %e %H:%M";
	tm = localtime(&h->mtime.tv_sec);
	if (!tm)
		fatal("localtime:");
	strftime(time, sizeof(time), timefmt, tm);
	if (h->type == '3' || h->type == '4')
		snprintf(info, sizeof(info), "%u, %u", major(h->dev), minor(h->dev));
	else
		snprintf(info, sizeof(info), "%ju", (uintmax_t)h->size);
	printf("%s %2d %-8s %-8s %9s %s %s", mode, 1, uname, gname, info, time, h->name);
	if (h->type == '1')
		printf(" == %s", h->linkname);
	putchar('\n');
}

int
main(int argc, char *argv[])
{
	const char *name = NULL, *arg;
	enum mode mode = LIST;
	struct header hdr;
	int (*readhdr)(FILE *, struct header *) = readpax;

	ARGBEGIN {
	case 'a':
		aflag = 1;
		break;
	case 'b':
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
		arg = EARGF(usage());
		while (*arg) {
			switch (*arg) {
			case 'a':
				break;
			case 'e':
				break;
			case 'm':
				break;
			case 'o':
				break;
			case 'p':
				break;
			default:
				break;
			}
		}
		//preserve = 
		break;
	case 'r':
		mode |= READ;
		break;
	case 's':
		fatal("-s not implemented");
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
		arg = EARGF(usage());
		if (strcmp(arg, "ustar") == 0)
			readhdr = readustar;
		else if (strcmp(arg, "pax") == 0)
			readhdr = readpax;
		else
			fatal("unsupported archive format '%s'", arg);
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

	switch (mode) {
	case LIST:
		for (;;) {
			if (readhdr(stdin, &hdr) == 0)
				break;
			if (opt.listopt) {
				fatal("listopt is not supported");
			} else if (vflag) {
				list(&hdr);
			} else {
				printf("%s\n", hdr.name);
			}
			skip(stdin, (hdr.size + 511) & ~511);
		}
		break;
	case READ:
		break;
	case WRITE:
		break;
	case COPY:
		break;
	}
}
