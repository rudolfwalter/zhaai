def FlagsForFile(filename, **kwargs):
	
	flags = [
		'-Weverything',
		'-Wno-missing-prototypes',
		'-Wno-missing-variable-declarations',
		'-Wno-switch-enum',
		'-fno-spell-checking',
		'-ansi',
		'-x', 'c',
		'-isystem', 'C:\\Bin\\msys64\\mingw64\\x86_64-w64-mingw32\\include',
		'-isystem', 'C:\\Bin\\msys64\\mingw64\\include'
	]
	
	return {
		'flags': flags,
		'do_cache': True
	}
