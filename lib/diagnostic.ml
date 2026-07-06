exception Error of string

let fail message = raise (Error message)
