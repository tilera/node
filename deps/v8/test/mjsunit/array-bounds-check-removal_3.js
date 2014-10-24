
var a = new Int32Array(1024);

function test_base(a, base) {
  a[base + 1] = 1;
}

test_base(a, 1);
test_base(a, 3);

assertEquals(1, a[4]);

test_base(a, 2048);
