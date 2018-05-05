class A {
  var a:array<array<int>>; // (1) : error CS0178 and error CS1586
  constructor(b: array<array<int>>) {
    //var a := b; // (2) : error CS0178 and error CS1586
    // a := b; // in combination with (1), or without it.
		/*a := new array<int>[b.Length];
		var i := 0;
		while i < b.Length
			invariant 0 <= i <= b.Length
		{
			a[i] := new int[b[i].Length];
			var j := 0;
			while j < b[i].Length
				invariant 0 <= j <= b[i].Length;
			{
				a[i][j] := b[i][j];
			}
		}*/
  }
}
method sub(a: array<array<int>>)
requires a.Length > 0
requires a[0].Length > 0
{
  print a[0][0];
  var b := a;
  print b[0][0];
}
method Main() {
  var a := new array<int>[2];
  a[0] := new int[2];
  a[0][0] := 42;
  print a[0][0];
  sub(a); // ok, no error
  var b := new A(a); // no error by itself (but well in combination with (1) or (2)).
}
