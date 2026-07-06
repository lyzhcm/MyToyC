let () =
  let _ast = Mytoyc.Driver.parse "int main() { return 1 + 2 * 3; }" in
  ()
