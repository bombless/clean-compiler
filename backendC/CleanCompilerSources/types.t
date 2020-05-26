
#if !defined (_THE__TYPES_)
#define _THE__TYPES_

#if defined (__MWERKS__) && defined (_X86_)
# define _WINDOWS_
#endif

#if (defined (__MWERKS__) && !defined (_X86_)) || defined (__MRC__)
# define POWER 1
#endif

#define NIL			0L

#define REALSIZE	2 /*1*/
#define FILESIZE	2

#define KBYTE		1024L

typedef unsigned Bool;
	enum {
		False = 0, True, MightBeTrue
	};

#endif
