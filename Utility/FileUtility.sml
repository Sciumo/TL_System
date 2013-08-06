structure FileUtility =
struct

local
    structure OFS = OS.FileSys
    structure OP = OS.Path
in
    fun mkDirs s =
        ignore (OFS.isDir s)
        handle SysErr =>
            (
                mkDirs (OP.dir s);
                OFS.mkDir s
            )
end

end (* struct *)
