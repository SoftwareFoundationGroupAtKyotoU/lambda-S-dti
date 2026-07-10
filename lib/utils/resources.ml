exception Resources_error of string

let marker = "libC/runtime.h"

let has_marker dir =
  Sys.file_exists (Filename.concat dir marker)

let installed_root_dir () =
  let exe = Sys.executable_name in
  let bin_dir = Filename.dirname exe in
  let prefix = Filename.dirname bin_dir in
  Filename.concat prefix "share/lambda-S-dti"

let ref_root_dir = ref ""

let find_root_dir () =
  let root =
    let installed = installed_root_dir () in
    (* let dir = Sys.getenv_opt "LSDTI_ROOT_DIR" in *)
    if has_marker installed then installed
    else 
      (* raise (Resources_error (Printf.sprintf "LSDTI_ROOT_DIR=%s does not contain %s" dir marker)) *)
      raise (Resources_error
            "cannot locate the lambda-S-dti project root (libC/runtime.h not found); \
             set LSDTI_ROOT_DIR to override")
  in
  ref_root_dir := root

let root_dir () = !ref_root_dir

let ensure_dir dir =
  if not (Sys.file_exists dir) then Sys.mkdir dir 0o755

let libc_dir () = Filename.concat (root_dir ()) "libC"

let result_c_dir () =
  let dir = Filename.concat (root_dir ()) "result_C" in
  ensure_dir dir;
  dir

let result_dir () =
  let dir = Filename.concat (root_dir ()) "result" in
  ensure_dir dir;
  dir
