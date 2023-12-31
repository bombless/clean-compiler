
# include "compiledefines.h"
# include "types.t"
# include "system.h"
# include "comsupport.h"
# include "backendsupport.h"

/*
	Utilities
	=========
*/
#define Debugger() { * (int *) NULL = 0; }

void
AssertionFailed (char *conditionString, char *file, int line)
{
	PutSStdError ("Error in backend: File ");
	PutSStdError (file);
	PutSStdError (", Line ");
	PutIStdError (line);
	PutSStdError (" (");
	PutSStdError (conditionString);
	PutSStdError (")\n");
} /* AssertionFailed */

void
fatal_backend_error (char *s)
{
	PutSStdError ("Error in backend: ");
	PutSStdError (s);
	PutCStdError ('\n');

	Debugger ();
}

#if 1
/*
	Memory management
	=================
*/

static enum {kMemoryInitClear, kMemoryInitSet} gMemoryInit = kMemoryInitSet;

# define	kDefaultConvertBufferSize	(32 * 1024)

typedef struct convert_buffer ConvertBufferS, *ConvertBufferP;

struct convert_buffer
{
	ConvertBufferP	cb_next;
	int				cb_size;
	char			cb_memory [kDefaultConvertBufferSize]; /* or more bytes */
};

static void
InvalidateMemory (void *memory, size_t size)
{
	char	value, *p;
	int		i;

	switch (gMemoryInit)
	{
		case kMemoryInitClear:
			value	= 0;
			break;
		case kMemoryInitSet:
			value	= ~0;
			break;
		default:
			Assert (False);
			break;
	}

	p	= memory;
	for (i = 0; i < size; i++)
		*p++	= value;
} /* InvalidateMemory */

static ConvertBufferP	gFirstBuffer = NULL, gCurrentBuffer = NULL;
static char 			*gMemory;
static long gBytesLeft = 0;

static void
AllocConvertBuffer (int min_size)
{
	ConvertBufferP	newBuffer;
	int new_convert_buffer_size;

	new_convert_buffer_size=kDefaultConvertBufferSize;
	while (new_convert_buffer_size<min_size)
		new_convert_buffer_size+=kDefaultConvertBufferSize;

	newBuffer	= (ConvertBufferP) malloc (sizeof (ConvertBufferS)+(new_convert_buffer_size-kDefaultConvertBufferSize));
	if (newBuffer == NULL)
		FatalCompError ("backendsupport.c", "AllocConvertBuffer", "out of memory");

	newBuffer->cb_size=new_convert_buffer_size;
	
	if (gFirstBuffer == NULL)
		gCurrentBuffer	= gFirstBuffer				= newBuffer;
	else
		gCurrentBuffer	= gCurrentBuffer->cb_next	= newBuffer;

	gCurrentBuffer->cb_next	=	NULL;

	gBytesLeft	= new_convert_buffer_size;
	gMemory		= gCurrentBuffer->cb_memory;

	InvalidateMemory (gMemory, new_convert_buffer_size);

	if (gFirstBuffer == NULL)
		gFirstBuffer	= gCurrentBuffer;
} /* AllocConvertBuffer */

void
FreeConvertBuffers (void)
{
	ConvertBufferP	buffer;

	buffer	= gFirstBuffer;

	while (buffer != NULL)
	{
		ConvertBufferP	nextBuffer;

		nextBuffer	= buffer->cb_next;

		InvalidateMemory (buffer,buffer->cb_size);
		free (buffer);

		buffer	= nextBuffer;
	}

	gFirstBuffer	= NULL;
	gCurrentBuffer	= NULL;
	gBytesLeft	= 0;
} /* FreeConvertBuffers */

void *
ConvertAlloc (SizeT size)
{
	void	*memory;

	size	= (size+3) & ~3;

	if (size > gBytesLeft){
		AllocConvertBuffer (size);

		if (size>gBytesLeft){
			static char s[100];
			
			strcpy (s,"ConvertAlloc: size = ");
			int_to_string (&s[strlen (s)],size);
			strcat (s,", gBytesLeft = ");
			int_to_string (&s[strlen (s)],gBytesLeft);
			fatal_backend_error (s);
		}
	}

	Assert (size <= gBytesLeft);

	memory	= gMemory;	
	gBytesLeft	-= size;
	gMemory	+=	size;

	return ((void *) memory);
} /* ConvertAlloc */
#endif