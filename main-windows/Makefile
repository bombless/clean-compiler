SHELL:=powershell.exe
SPACE:=$(eval) $(eval)
COMMA:=,

OBJS:=cDirectory.obj c_set_return_code.obj c_thread_message.obj

all: $(OBJS)
	mkdir -f "Clean System Files" | Out-Null
	copy $(subst $(SPACE),$(COMMA),$(OBJS)) "Clean System Files"

$(OBJS): %.obj: %.c
	cl /nologo /I ..\nitrile-packages\windows-x64\base-rts\misc\src /O2 /GS- /c $< /Fo"$@"
