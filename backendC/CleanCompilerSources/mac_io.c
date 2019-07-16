
#include "compiledefines.h"

#ifdef KARBON
# define TARGET_API_MAC_CARBON 1
#endif

#define for_l(v,l,n) for(v=(l);v!=NULL;v=v->n)

#if defined (applec) || defined (__MWERKS__) || defined (__MRC__) || defined (GNU_C)
#	define mpwc
#endif

#ifdef MAKE_MPW_TOOL
# define NO_CLEAN_SYSTEM_FILES_FOLDERS
# define NEWBRIDGE
#endif

#if defined (mpwc) /* && ! (defined (MAKE_MPW_TOOL) && !defined (MAIN_CLM)) */
#	define USE_PATH_CACHE 1
#else
#	define USE_PATH_CACHE 0
#endif

#ifndef _SYSTEM_
#	include "types.t"
#	include "system.h"
#endif

#if defined (POWER)
#	define USE_SYSTEM_ALLOC 1
#else
#	define USE_SYSTEM_ALLOC 0
#endif

#include <stdio.h>
#ifndef mpwc
#	include <pascal.h>
#endif
#include <Files.h>
#include <Memory.h>
#ifndef mpwc
#	include <strings.h>
#endif
#include <Devices.h>
#include <Events.h>
#ifdef KARBON
# include <Script.h>
#endif
#ifndef mpwc
#	include <unix.h>
#endif
#if USE_PATH_CACHE
#	include "path_cache.h"
#endif

#undef FOLDER_DOES_NOT_EXIST_ERRORS

static unsigned char *copy_c_to_p_string (char *c_string,char *p_string)
{
	char *s,*d,c;
	
	d=p_string+1;
	s=c_string;
	while (c=*s++, c!='\0')
		*d++=c;
	
	*p_string=s-1-c_string;
	
	return (unsigned char*) p_string;
}

#ifdef KARBON
	static int FindFileUTCDateTime0 (char *fname,UTCDateTime *file_time_p)
	{
		int err;
		FSCatalogInfo catalog_info;
		FSRef fs_ref;
		FSSpec fs_spec;

		copy_c_to_p_string (fname,(char*)&fs_spec.name);
		fs_spec.parID=0;
		fs_spec.vRefNum=0;

		err = FSpMakeFSRef (&fs_spec,&fs_ref);
		if (err)
			return 0;

		err = FSGetCatalogInfo (&fs_ref,kFSCatInfoContentMod,&catalog_info,NULL,NULL,NULL);
		if (err)
			return 0;
		else {
			*file_time_p=catalog_info.contentModDate;

			return 1;	
		}
	}

	static int FindFileUTCDateTime (char *fname,struct vd_id vd_id,UTCDateTime *file_time_p)
	{
		int err;
		FSCatalogInfo catalog_info;
		FSRef fs_ref;
		FSSpec fs_spec;

		copy_c_to_p_string (fname,(char*)&fs_spec.name);
		fs_spec.parID=vd_id.directory_id;
		fs_spec.vRefNum=vd_id.volume_id;

		err = FSpMakeFSRef (&fs_spec,&fs_ref);
		if (err)
			return 0;

		err = FSGetCatalogInfo (&fs_ref,kFSCatInfoContentMod,&catalog_info,NULL,NULL,NULL);
		if (err!=0)
			return 0;
		else {
			*file_time_p=catalog_info.contentModDate;

			return 1;	
		}
	}
#else
	static FileTime FindFileTime (char *fname,int wd_ref_num)
	{
		int err;
		FileParam fpb;
		char p_string [256];

		fpb.ioNamePtr=copy_c_to_p_string (fname,p_string);
		fpb.ioFDirIndex=0;
		fpb.ioFVersNum=0;
		fpb.ioVRefNum=wd_ref_num;

#ifdef KARBON
		err = PBHGetFInfo ((HParmBlkPtr)&fpb,0);
#else
# ifdef mpwc
		err = PBGetFInfoSync ((ParmBlkPtr)&fpb);
# else
		err = PBGetFInfo (&fpb, 0);
# endif
#endif

		if (err)
			return NoFile;
		else
			return fpb.ioFlMdDat;
	}
#endif

char *PATHLIST;

#ifdef mpwc
struct path_list {
# ifdef KARBON
	struct vd_id		path_vd_id;
	struct vd_id		path_clean_system_files_vd_id;
# else
	short				path_wd_ref_num;
	short				path_clean_system_files_wd_ref_num;
# endif
	struct path_list *	path_next;
#if defined (__MWERKS__) || defined (__MRC__)
	char				path_name[];
#else
	char				path_name[0];
#endif
};

static struct path_list *path_list=NULL;

static void add_directory_to_path_list (char *path_name,struct path_list **old_path_list_h)
{
	struct path_list *new_path,**last_path_p;
	int path_name_length;
	char p_string [256];
#ifdef KARBON
	struct vd_id vd_id,clean_system_files_vd_id;
	FSSpec fs_spec;
	FSRef fs_ref;
#else
	short wd_ref_num,clean_system_files_wd_ref_num;
	CInfoPBRec fpb;
	WDPBRec wd_pb;
#endif
	int err,root_path;

	root_path=0;

	if (path_name){
		char *p;
		
		for (p=path_name; *p!=':' && *p!='\0'; ++p)
			;
			
		if (*p=='\0'){
			root_path=1;
			p[0]=':';
			p[1]='\0';
		}
	}

#ifdef KARBON
	vd_id.volume_id=0;
	vd_id.directory_id=0;
	err = FSMakeFSSpec (0,0,path_name ? copy_c_to_p_string (path_name,p_string) : (unsigned char*)"\001:",&fs_spec);
	if (err==0){
		err = FSpMakeFSRef (&fs_spec,&fs_ref);
		if (err==0){
			FSCatalogInfo catalog_info;
			
			err = FSGetCatalogInfo (&fs_ref,kFSCatInfoVolume|kFSCatInfoNodeID,&catalog_info,NULL,NULL,NULL);
			
			if (err==0){
				vd_id.volume_id=catalog_info.volume;
				vd_id.directory_id=catalog_info.nodeID;
			}
		}
	}
#else
	if (path_name)
		fpb.hFileInfo.ioNamePtr=copy_c_to_p_string (path_name,p_string);
	else
		fpb.hFileInfo.ioNamePtr=(unsigned char*)"\001:";

	fpb.hFileInfo.ioVRefNum=0;
	fpb.hFileInfo.ioFDirIndex=0;
	fpb.hFileInfo.ioDirID=0;

	err = PBGetCatInfoSync (&fpb);
#endif

	if (err!=0){
#ifdef FOLDER_DOES_NOT_EXIST_ERRORS
		if (path_name)
			fprintf (stderr,"folder '%s' does not exist\n",path_name);
# ifdef ADD_NULL_PATH 
		else
			fprintf (stderr,"folder ':' does not exist\n");
# endif
#endif
		return;
	}

#ifndef KARBON
	wd_pb.ioNamePtr=fpb.hFileInfo.ioNamePtr;
	wd_pb.ioWDProcID='ClCo';

	wd_pb.ioVRefNum=0;
	wd_pb.ioWDDirID=0;
/*
	wd_pb.ioVRefNum=fpb.hFileInfo.ioVRefNum;
	wd_pb.ioWDDirID=fpb.hFileInfo.ioDirID;
*/
	err = PBOpenWD (&wd_pb,0);
	if (err!=0){
		if (path_name)
			fprintf (stderr,"folder '%s' does not exist\n",path_name);
#ifdef ADD_NULL_PATH 
		else
			fprintf (stderr,"folder ':' does not exist\n");
#endif
		return;
	}

	wd_ref_num=wd_pb.ioVRefNum;
#endif

#ifndef NO_CLEAN_SYSTEM_FILES_FOLDERS
	if (path_name){
		if (root_path)
			strcat (path_name,"Clean System Files");
		else
			strcat (path_name,":Clean System Files");
	} else
		path_name="Clean System Files";

# ifdef KARBON
	clean_system_files_vd_id.volume_id=0;
	clean_system_files_vd_id.directory_id=0;
	err = FSMakeFSSpec (0,0,copy_c_to_p_string (path_name,p_string),&fs_spec);

	if (err==fnfErr){
		long dir_id;
		
		err=FSpDirCreate (&fs_spec,smSystemScript,&dir_id);
	}

	if (err==0){
		err = FSpMakeFSRef (&fs_spec,&fs_ref);
		if (err==0){
			FSCatalogInfo catalog_info;
			
			err = FSGetCatalogInfo (&fs_ref,kFSCatInfoVolume|kFSCatInfoNodeID,&catalog_info,NULL,NULL,NULL);
			
			if (err==0){
				clean_system_files_vd_id.volume_id=catalog_info.volume;
				clean_system_files_vd_id.directory_id=catalog_info.nodeID;
			}
		}
	}
	
	if (err!=0){
		fprintf (stderr,"cannot create folder '%s'\n",path_name);

		return;	
	}
# else
	fpb.hFileInfo.ioNamePtr=copy_c_to_p_string (path_name,p_string);
	fpb.hFileInfo.ioVRefNum =0;
	fpb.hFileInfo.ioFDirIndex=0;
	fpb.hFileInfo.ioDirID=0;

	err = PBGetCatInfoSync (&fpb);

	if (err!=0){
		err = PBDirCreateSync ((HParamBlockRec*)&fpb);

		if (err!=0){
			fprintf (stderr,"cannot create folder '%s'\n",path_name);

			return;
		}
	}

	wd_pb.ioNamePtr=fpb.hFileInfo.ioNamePtr;
	wd_pb.ioWDProcID='ClCo';

	wd_pb.ioVRefNum=0;
	wd_pb.ioWDDirID=0;
/*
	wd_pb.ioVRefNum=fpb.hFileInfo.ioVRefNum;
	wd_pb.ioWDDirID=fpb.hFileInfo.ioDirID;
*/
	err = PBOpenWD (&wd_pb,0);
	if (err!=0){
		if (path_name)
			fprintf (stderr,"folder '%s' does not exist\n",path_name);
		return;
	}

	clean_system_files_wd_ref_num=wd_pb.ioVRefNum;
# endif

	path_name_length=strlen (path_name)-strlen (":Clean System Files");
	if (path_name_length<0)
		path_name_length=0;
	path_name[path_name_length]='\0';
#else
	clean_system_files_wd_ref_num=0;
		
	if (path_name==NULL)
		path_name="";
		
	path_name_length=strlen (path_name);
#endif

	last_path_p=&path_list;
	while (*last_path_p)
		last_path_p=&(*last_path_p)->path_next;

	/* reuse memory from previous path_list */
	{
		struct path_list *old_path_list_p;

		for (; (old_path_list_p=*old_path_list_h)!=NULL; old_path_list_h=&old_path_list_p->path_next){
			if (
#ifdef KARBON
				old_path_list_p->path_vd_id.volume_id==vd_id.volume_id &&
				old_path_list_p->path_vd_id.directory_id==vd_id.directory_id &&
				old_path_list_p->path_clean_system_files_vd_id.volume_id==clean_system_files_vd_id.volume_id &&
				old_path_list_p->path_clean_system_files_vd_id.directory_id==clean_system_files_vd_id.directory_id &&
#else
				old_path_list_p->path_wd_ref_num==wd_ref_num &&
				old_path_list_p->path_clean_system_files_wd_ref_num==clean_system_files_wd_ref_num &&
#endif
				!strcmp (old_path_list_p->path_name,path_name))
			{
				*old_path_list_h=old_path_list_p->path_next;

				old_path_list_p->path_next=NULL;
				*last_path_p=old_path_list_p;
				return;
			}
		}
	}
	
	new_path=(struct path_list*)Alloc (1,sizeof (struct path_list)+1+path_name_length);
#ifdef KARBON
	new_path->path_vd_id=vd_id;
	new_path->path_clean_system_files_vd_id=clean_system_files_vd_id;
#else
	new_path->path_wd_ref_num=wd_ref_num;
	new_path->path_clean_system_files_wd_ref_num=clean_system_files_wd_ref_num;
#endif
	strcpy (new_path->path_name,path_name);
	new_path->path_next=NULL;

	*last_path_p=new_path;
}
#endif

extern char *path_parameter;

void GetInitialPathList (void)
{
	char path[MAXPATHLEN];
	struct path_list *old_path_list;
	char *s,*path_elem,*p;
	int c;

	p = path_parameter;

	if (p==NULL){
		PATHLIST="\0";
		return;
	}

	PATHLIST = p;
	
	old_path_list=path_list;

	path_list=NULL;

#ifdef ADD_NULL_PATH
	add_directory_to_path_list (NULL,&old_path_list);
#endif

    path_elem =PATHLIST;

    s=path_elem;
	for (c = *s;;c = *s){
		if (c == ',' || c == '\0'){
			char *from_p,*dest_p;
			
			from_p=path_elem;
			dest_p=path;
			while (from_p<s)
				*dest_p++ = *from_p++;
			*dest_p = '\0';
			
			add_directory_to_path_list (path,&old_path_list);
		    		    
		    if (c == '\0')
				break;
		    
			path_elem = ++s;
		} else
		    ++s;
    }
}

void FreePathList (void)
{
	struct path_list *path,*next_path;
	
	path=path_list;
	path_list=NULL;

	while (path!=NULL){
		next_path=path->path_next;
		Free (path);
		path=next_path;
	}
}

char *GetFileExtension (FileKind kind)
{
	switch (kind){
		case abcFile:		return ".abc";
		case obj00File:		return ".obj0";
		case obj20File:		return ".obj1";
		case obj81File:		return ".obj2";
		case iclFile:		return ".icl";
		case dclFile:		return ".dcl";
		case dumpFile:		return ".dmp";
		case statFile:		return ".stt";
		case stasFile:		return ".str";
		case assFile:		return ".a";
		case sunAssFile:	return ".s";
		case helpFile:
		case applFile:
		case otherFile:
		default:			return "";
	}	
}

#ifdef NEWBRIDGE
extern char *clean_abc_path; /* imported from clm.c */
#endif

#ifdef mpwc
	static Bool findfilepath (char *file_name,FileKind kind,char *path)
	{
		char *file_extension;
		int in_clean_system_files_folder;
		struct path_list *path_elem;
	
		switch (kind){
			case abcFile:
			case obj00File:
			case obj20File:
			case obj81File:
				in_clean_system_files_folder=1;
				break;
			default:
				in_clean_system_files_folder=0;
		}

		file_extension=GetFileExtension (kind);

		if (file_name[0]!=':'){
			strcpy (path,file_name);
			strcat (path,file_extension);

#if USE_PATH_CACHE
			if (kind==dclFile){
				struct search_dcl_path_in_cache_result r;
				
				if (search_dcl_path_in_cache (file_name,&r)){
					strcpy (path,r.path);

#ifndef NO_CLEAN_SYSTEM_FILES_FOLDERS
					if (path[0]=='\0'){
						if (in_clean_system_files_folder)
							strcpy (path,"Clean System Files:");
					} else
						if (in_clean_system_files_folder)
							strcat (path,":Clean System Files:");
						else
							strcat (path,":");
#else
					if (path[0]!='\0' && path[strlen (path)-1]!=':')
						strcat (path,":");
#endif

					strcat (path,file_name);
					strcat (path,file_extension);
										
					return True;
				}
			}
#endif

#ifdef NEWBRIDGE
			for (path_elem=(clean_abc_path!=NULL && !in_clean_system_files_folder && path_list!=NULL)
							? path_list->path_next 
							: path_list;
				 path_elem!=NULL;
				 path_elem=(clean_abc_path!=NULL && in_clean_system_files_folder)
				 			? NULL
				 			: path_elem->path_next)
			{
#else
			for_l (path_elem,path_list,path_next){
#endif
#ifdef KARBON
				struct vd_id vd_id;
				FileTime file_time;

# ifndef NO_CLEAN_SYSTEM_FILES_FOLDERS
				if (in_clean_system_files_folder)
					vd_id=path_elem->path_clean_system_files_vd_id;
				else
# endif
					vd_id=path_elem->path_vd_id;
	
				if (FindFileUTCDateTime (path,vd_id,&file_time)){
#else
				short wd_ref_num;
				unsigned long file_time;

# ifndef NO_CLEAN_SYSTEM_FILES_FOLDERS
				if (in_clean_system_files_folder)
					wd_ref_num=path_elem->path_clean_system_files_wd_ref_num;
				else
# endif
					wd_ref_num=path_elem->path_wd_ref_num;
	
				file_time=FindFileTime (path,wd_ref_num);

				if (file_time!=NoFile){
#endif
					strcpy (path,path_elem->path_name);

#ifndef NO_CLEAN_SYSTEM_FILES_FOLDERS
					if (path[0]=='\0'){
						if (in_clean_system_files_folder)
							strcpy (path,"Clean System Files:");
					} else
						if (in_clean_system_files_folder)
							strcat (path,":Clean System Files:");
						else
							strcat (path,":");
#else
					if (path[0]!='\0' && path[strlen (path)-1]!=':')
						strcat (path,":");
#endif

					strcat (path,file_name);
					strcat (path,file_extension);

#if USE_PATH_CACHE
					if (kind==dclFile && !in_clean_system_files_folder)
						cache_dcl_path (file_name,
# ifdef KARBON
							path_elem->path_vd_id,path_elem->path_clean_system_files_vd_id,
# else
							path_elem->path_wd_ref_num,path_elem->path_clean_system_files_wd_ref_num,
# endif
							file_time,path_elem->path_name);
#endif						
					return True;
				}
			}
#ifdef NEWBRIDGE
			return False;
#endif
		}


#ifndef NO_CLEAN_SYSTEM_FILES_FOLDERS
		if (in_clean_system_files_folder && file_name[0]!=':'){
			strcpy (path,":Clean System Files:");
			strcat (path, file_name);
		} else
#endif
		strcpy (path,file_name);
	
		strcat (path,file_extension);
	
# ifdef KARBON
		{
			FileTime file_time;
			return FindFileUTCDateTime0 (path,&file_time);
		}
# else
		return FindFileTime (path,0)!=NoFile;
# endif
	}
#else
	static Bool findfilepath (char *wname, FileKind kind, char *path)
	{
		char *s,*pathelem,c,*file_extension;
		FILE *f;
		
		file_extension=GetFileExtension (kind);
		
		/* first try current directory */
		strcpy (path,wname);
		strcat (path,file_extension);
	
# ifdef KARBON
		if (FindFileUTCDateTime0 (path) != NoFile)
# else
		if (FindFileTime (path,0) != NoFile)
# endif
			return True;
		
		pathelem = PATHLIST;

		s = pathelem;	
		for (c = *s;;c = *s){
			if (c == ',' || c == '\0'){
				char *from_p,*dest_p;
				
				from_p=path_elem;
				dest_p=path;
				while (from_p<s)
					*dest_p++ = *from_p++;
				*dest_p = '\0';
				
				strcat (path, ":");
				strcat (path, wname);
				strcat (path,file_extension);
				
#ifdef KARBON
				if (FindFileUTCDateTime0 (path) != NoFile)
#else
				if (FindFileTime (path,0) != NoFile)
#endif
					return True;
							
				/* if all else fails, exit the loop */
				if (c == '\0')
					break;
				
				pathelem = ++s;
			} else
				++s;
		}
	
		/* if all else fails, return False, and the current name */
		strcpy (path,wname);
		strcat (path,file_extension);
	
		return False;
	}
#endif

#if defined (GNU_C)
char *convert_file_name (char *file_name,char *buffer)
{
	CFURLRef hfs_url;
	CFStringRef	hfs_string, posix_string;
	
	hfs_string = CFStringCreateWithCString (NULL/*kCFAllocatorDefault*/,file_name,kCFStringEncodingMacRoman);
	hfs_url = CFURLCreateWithFileSystemPath (NULL/*kCFAllocatorDefault*/,hfs_string,kCFURLHFSPathStyle,/*isDirectory*/false);
	CFRelease (hfs_string);
	posix_string = CFURLCopyFileSystemPath (hfs_url,kCFURLPOSIXPathStyle);
	CFRelease (hfs_url);
	if (! CFStringGetCString (posix_string,buffer,512,kCFStringEncodingMacRoman)){
		CFRelease (posix_string);
		return NULL;
	}
	return buffer;
}

static FILE *fopen_with_file_name_conversion (char *file_name,char *mode)
{
	char buffer[512+1];

	file_name=convert_file_name (file_name,buffer);
	if (file_name==NULL)
		return NULL;

	return fopen (file_name,mode);
}

# define fopen fopen_with_file_name_conversion
#endif

#if 0
extern File rules_file;
#endif

File FOpen (char *file_name,FileKind kind, char *mode)
{
	char path[MAXPATHLEN];
	Bool res;

#ifdef mpwc
	if (mode[0]=='r'){
		findfilepath (file_name,kind,path);

# if 0
		FPrintF (rules_file,"%s\n",path);
# endif

		return (File) fopen (path, mode);
	} else {
		char *p;
		int full_path_name;
				
		for (p=file_name; *p!=':' && *p!='\0'; ++p)
			;
		full_path_name = *p==':';

		if (full_path_name){
			strcpy (path,file_name);
			strcat (path,GetFileExtension (kind));
			return (File) fopen (path,mode);			
		} else {
			res = findfilepath (file_name,dclFile, path);
			if (!res)
				res = findfilepath (file_name,iclFile, path);

			if (res){
				char *p,*after_last_colon;

				after_last_colon=NULL;

				p=path;
				while (*p)
					if (*p++==':')
						after_last_colon=p;
				
				if (after_last_colon==NULL){
					after_last_colon=path;
					*after_last_colon++=':';
				}
#ifndef NO_CLEAN_SYSTEM_FILES_FOLDERS
				strcpy (after_last_colon,"Clean System Files:");
#endif
				strcat (after_last_colon,file_name);
			    strcat (after_last_colon,GetFileExtension (kind));
				
				return (File) fopen (path, mode);
			} else
				return (File) Null;
		}
	}
#else
	res=findfilepath (file_name, kind, path);

	if (res || mode[0] != 'r')
		return (File) fopen (path, mode);
	else
		return (File) Null;
#endif
}

int FClose (File f)
{
	return fclose ((FILE *) f);
}

extern int FDelete (char *fname, FileKind kind);

int FDelete (char *fname, FileKind kind)
{
	char path[MAXPATHLEN];
	Bool res;
	
	res = findfilepath (fname, kind, path);

	if (res)
		return remove (path);
	else
		return -1;
}

#define OUTSIZE 2048

int FPrintF (File f, char *fmt, ...)
{	int n;
	va_list args;
	char outbuffer[OUTSIZE];
	
	va_start (args, fmt);

	vsprintf (outbuffer, fmt, args);
	
	n = strlen (outbuffer);
	if (n >= OUTSIZE)
	{	fputs ("FATAL ERROR: out buffer to small\n", stderr);
		exit (1);
	}

	va_end (args);

	return fputs (outbuffer, (FILE *) f);
} /* FPrintF */

int FPutS (char *s, File f)
{
	return fputs (s, (FILE *) f);
} /* FPutS */

void DoFatalError (char *fmt, ...)
{	va_list args;
	
	va_start (args, fmt);
	
	fputs ("Fatal error: ", stderr);
	(void) vfprintf (stderr, fmt, args);
	va_end (args);

	exit (0);
}

void CmdError (char *errormsg,...)
{	va_list args;
	
	va_start (args, errormsg);

	fputs ("Command line error: ", stdout);
	vfprintf (stdout, errormsg, args);
	fputc ('\n', stdout); 
		
	va_end (args);
}

void Free (void *p)
{		
#if USE_SYSTEM_ALLOC
	DisposePtr ((char*)p);
#else
	free ((char *) p);
#endif
}
