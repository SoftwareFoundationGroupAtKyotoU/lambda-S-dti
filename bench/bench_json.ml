let float x = `Float x
let int x = `Int x
let str s = `String s
let list xs = `List xs
let obj xs = `Assoc xs

let to_channel_ln oc (j:Yojson.Safe.t) =
  Yojson.Safe.to_channel oc j; output_char oc '\n'