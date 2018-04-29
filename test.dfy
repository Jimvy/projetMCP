method firstTest() returns (/*a: array<array<int>>*/) {
	var fnc := new array<int>[3];
	fnc[0] := new int[2];
	fnc[1] := new int[3];
	fnc[2] := new int[2];
	fnc[0][0] :=  1;
	fnc[0][1] := -2;
	fnc[1][0] := -1;
	fnc[1][1] :=  3;
	fnc[1][2] := -4;
	fnc[2][0] :=  2;
	fnc[2][1] := -3;
	assert fnc.Length == 3;
	assert fnc[0].Length == 2;
	assert fnc[0][0] == 1;
	var i := 0;
	while i < fnc.Length
		invariant 0 <= i <= fnc.Length;
	{
		var j := 0;
		while j < fnc[i].Length
			invariant 0 <= j <= fnc[i].Length;
		{
			print fnc[i][j];
			j := j+1;
		}
		i := i+1;
	}
	//a := fnc;
	hd(fnc);
}
method hd(a: array<array<int>>)
	requires a.Length > 0
	requires a[0].Length > 0
{
	print a[0][0];
	var b := a;
	print b[0][0];
}
class A {
	var a: array<array<int>>;
	constructor(b: array<array<int>>) {
		a := b;
	}
}
method secondTest() {
	//var a1 := new array<int>;
	//var a: array<array<int>>;
	//a := new array<int>[2];// [new int[3], new int[3]];
	var b: array<int>;
	b := new int[3];
	var c := new int[4];
	var d := new array<int>[5];
	d[0] := new int[3];
	hd(d);
	var e := new A(d);
}
method Main() {
	/*var a := */firstTest();
	//print a;
	secondTest();
	var tab := new int[0];
	var tab2 := new int[5];
	var i := 0;
	while i < 5
		invariant 0 <= i <= 5
	{
		print tab2[i];
		i := i+1;
	}
}
