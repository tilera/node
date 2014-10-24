

function array_natives_test() {

  // Splice
  var a3 = [1,2,3];
  var a3r;
  a3 = [1.1,2,3];
  a3r = a3.splice(0, 0, 2.1);
  print(a3);
}

array_natives_test();
