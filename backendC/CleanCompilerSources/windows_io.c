
#ifdef __MWERKS__
#	define _WINDOWS_
#endif

#include "compiledefines.h"
#include "system.h"
#include <stdio.h>

#ifdef _WIN64
# undef _WINDOWS_
# include <windows.h>
#else
# ifdef __MWERKS__
#	include <x86_prefix.h>
# else
#	define _X86_
# endif
# include <windef.h>
# include <winbase.h>
#endif

File FOpen (char *fname,char *mode)
{
	return fopen (fname,mode);
}

int FClose (File f)
{
	return fclose ((FILE *) f);
}

int FDelete (char *fname)
{
	return remove (fname);
}

int FPutS (char *s, File f)
{
	return fputs (s, (FILE *) f);
}
