
extern int MACVAR;
#define CheckVersion if (MACVAR != VERSION) DoFatalError ("Wrong version number")

typedef short          TwoBytesInt;
typedef int            FourBytesInt;
typedef unsigned short TwoBytesUnsigned;
typedef unsigned int   FourBytesUnsigned;

typedef double  EightBytesReal;
typedef float         FourBytesReal;

#define SizeT		unsigned long
#define SizeOf(A)	((SizeT) sizeof (A))

#include <limits.h>
#define MAXUNSIGNED	ULONG_MAX

#define _VARARGS_

#include <string.h>
#include <stdlib.h>

#if defined (__MWERKS__) || defined (_WINDOWS_)
#	include <stdio.h>
#else
#	include <unix.h>
#endif

#include <setjmp.h>
#include <stdarg.h>

typedef FILE *File;

/* special for MacIntosh command line support */
extern void InitIO (void);
extern void GetPreferences (char *fname);

#define StdOut stdout
#define StdError stderr
#define StdVerboseH stdout
#define StdVerboseL stdout
#define StdTrace stdout
#define StdDebug stdout;
#define StdListTypes stdout

#define FGetC(f) fgetc(f)
#define FPutC(c,f) fputc(c,f)
