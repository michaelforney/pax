#define _POSIX_C_SOURCE 200809L
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <fnmatch.h>
#include <regex.h>
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
	time_t atime, mtime;
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
} opt;
static const char *exthdr_name;
static const char *globexthdr_name;
static struct replstr *repl;

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
	char c;
	unsigned long long n;

	n = 0;
	while (len > 0) {
		c = *str;
		if (c == ' ' || c == '\0')
			break;
		if (c < '0' || c > '8')
			fatal("invalid ustar number field");
		n = n * 8 + (c - '0');
		++str;
		--len;
	}
	if (len == 0)
		fatal("invalid ustar number field: missing terminator");
	return n;
}

static int
readustar(FILE *f, struct header *h)
{
	char buf[512], *end, *p;
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
	if (!h->name) {
		namelen = strnlen(buf, 100);
		prefixlen = strnlen(buf + 345, 155);
		if (namelen == 100 || prefixlen > 0) {
			h->name = malloc(namelen + prefixlen + 2);
			if (!h->name)
				fatal("malloc:");
			memcpy(h->name, buf, namelen);
			h->name[namelen] = '\0';
			memcpy(h->name + namelen + 1, buf + 345, prefixlen);
			h->name[namelen + 1 + prefixlen] = '\0';
		} else {
			h->name = buf;
		}
	}

	buf[107] = '\0';
	h->mode = strtoul(buf + 100, &end, 8);

	h->size = octnum(buf + 124, 12);

	h->type = buf[156];
	
	if (!h->linkname) {
		linklen = strnlen(buf + 157, 100);
		if (linklen == 100) {
			h->linkname = malloc(linklen + 1);
			if (!h->linkname)
				fatal("malloc:");
			memcpy(h->linkname, buf + 157, linklen);
			h->linkname[linklen] = '\0';
		}
	}
	if (memcmp(buf + 263, "00", 2) != 0)
		fatal("invalid header version");
	h->uname = buf + 265;
	if (!memchr(h->uname, '\0', 32))
		fatal("uname is not NUL-terminated");
	h->gname = buf + 297;
	if (!memchr(h->gname, '\0', 32))
		fatal("gname is not NUL-terminated");
	if (h->type == '3' || h->type == '4') {
		major = octnum(buf + 329, 8);
		minor = octnum(buf + 337, 8);
		h->dev = makedev(major, minor);
	}

	return 1;
}

static void
extkeyval(struct header *h, const char *key, const char *val, size_t vallen)
{
	char *end;

	if (strcmp(key, "atime") == 0) {
		h->atime = strtoull(val, &end, 10);
		if (end != val + vallen)
			fatal("invalid extended header: bad atime");
	} else if (strcmp(key, "charset") == 0) {
	} else if (strcmp(key, "comment") == 0) {
		/* ignore */
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
		h->mtime = strtoull(val, &end, 10);
		if (end != val + vallen)
			fatal("invalid extended header: bad mtime");
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

static int
readexthdr(FILE *f, struct header *h, size_t len)
{
	static char *rec = NULL;
	static size_t reccap = 0;
	size_t reclen, vallen, off, pad;
	char *key, *val;

	pad = 512 - len % 512;
	while (len > 0) {
		if (fscanf(f, "%zu %zn", &reclen, &off) != 1)
			fatal("invalid extended header: invalid record");
		if (reclen <= off || reclen > len)
			fatal("invalid extended header: record has invalid length");
		len -= reclen;
		reclen -= off;
		if (reccap < reclen) {
			rec = realloc(rec, reclen);
			if (!rec)
				fatal(NULL);
			reccap = reclen;
		}
		if (fread(rec, 1, reclen, f) != reclen) {
			if (ferror(f))
				fatal("read:");
			fatal("archive truncated");
		}
		key = rec;
		val = strchr(rec, '=');
		if (!val)
			fatal("invalid extended header: record has no '='", rec);
		*val++ = '\0';
		vallen = reclen - (val - rec) - 1;
		if (val[vallen] != '\n')
			fatal("invalid extended header: record is missing newline");
		val[vallen] = '\0';
		//extkeyval
	}
	skip(f, pad);
}

static int
readpax(FILE *f, struct header *h)
{
	static struct header global;
	struct header local = {0};

	for (;;) {
		if (readustar(f, h) == 0)
			return 0;
		switch (h->type) {
		case 'g':
			readexthdr(f, &global, h->size);
			break;
		case 'x':
			readexthdr(f, &local, h->size);
			break;
		default:
			return 1;
		}
	}
}

static int
readhdr(FILE *f, struct header *h)
{

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
			fatal("option 'listopt' not implemented");
		} else if (strcmp(key, "times") == 0) {
			if (val)
				fatal("option 'times' should not have a value");
		} else {
			//extkeyval(key, val);
		}
	}
}

int
main(int argc, char *argv[])
{
	const char *name = NULL, *arg;
	enum mode mode = LIST;
	struct header hdr;
	void (*readhdr)(FILE *, struct header *);

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
		if (strcmp(arg, "cpio") == 0) {
			
		}
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

	switch (mode) {
	case LIST:
		for (;;) {
			if (readpax(stdin, &hdr) == 0)
				break;
			if (vflag) {
			} else {
				printf("%s\n", hdr.name);
			}
			skip(stdin, hdr.size + 512 - hdr.size % 512);
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
