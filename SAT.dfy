
//datatype Solution = array<int>
function abs(x: int): int {
	if x >= 0 then x else -x
}
predicate okClause(tab: array<int>, np: int)
	reads tab
{
	forall j | 0 <= j < tab.Length :: abs(tab[j]) <= np && tab[j] != 0
}
predicate okFNC(fnc: array<array<int>>, np: int)
	reads fnc, fnc[..]
{
	forall i | 0 <= i < fnc.Length :: okClause(fnc[i], np)
}

// Abstraction
class SAT {
//_______________________VARIABLES________________________________________
	var n :int ; // nombre de variables dans la FNC, et donc plus grand index de variable.
	var clauses : array<array<int>>;
  //TODO //probleme : tableau de clause
  //TODO

//_____________________INVARIANTS_________________________________
// SAT 
//TODO
//cree le tableau de clause ???
//initialise sol= int[maxLenght]
//return solve(sol,0)
	predicate ok()
		reads this, clauses, clauses[..]
	{
		okFNC(clauses, n) && n >= 0
	}
	predicate okSol(sol: array<int>, ind: int)
		reads this, sol
		requires 1 <= ind <= n+1
	{
		sol.Length >= n+1 && sol[0] == 0 && forall k | 1 <= k < ind :: (sol[k] == k || sol[k] == -k) && forall k | ind <= k <= n :: sol[k] == 0
	}

	constructor (fnc: array<array<int>>, np: int)
		requires np >= 0
		requires okFNC(fnc, np)
		ensures ok()
	{
		clauses := fnc;
		n := np;
	}

	method isSatisfiable() returns (b: bool)
		requires ok()
	{
		var sol := new int[n+1]; // L'élément 0 est ignoré.
		b := solve(sol, 1);
	}

	method solve(sol: array<int>, ind: int) returns (b : bool)
		requires 1 <= ind <= n+1
		requires sol.Length >= n+1
		//requires okSol(sol, ind)
		modifies sol
		decreases sol.Length - ind
  {
    if ind < n {
      sol[ind] := ind;
      var solved := solve(sol,ind + 1);
      if solved{
        return true; 
      }
      else{ 
        sol[ind] := -ind;
        solved := solve(sol,ind + 1);
        return solved;
      }
    } else { //ind == maxLenght
      var check := checkSolution(sol);
      return check;
    }
  }

	method checkSolution(sol : array<int> ) returns (b : bool)
  {
    var i := 0;
    while i< clauses.Length
      decreases clauses.Length-i;
    {
      var check:bool := checkClause(sol , clauses[i]);
      if !check 
      {
        return false;
      }
      i := i+1;
    }
    return true ;
  }

	method checkClause(sol : array<int> , cl : array<int>) returns (b : bool)
  {
    var i := 0;
    while i< cl.Length
      decreases cl.Length - i;
    {
      var elem:int := cl[i];
      //version courte de for s in sol { if(s == elem){ return true} }
      //if (elem == sol[i]) { //ca va etre super dur a prouver
      if(elem == 2){ //to remove
        return true;
      }
      i := i+1;
    }
    return false;
  }
}

method firstTest() {
	// (A or -B) and (-A or C or -D) and (B or -C)
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
	var sat1 := new SAT(fnc, 4);
	var isSat := sat1.isSatisfiable();
	//assert isSat;
}
method secondTest() {
	// (A or B) and (-A) and (-B)
  var fnc := new array<int>[3];
	fnc[0] := new int[2];
	fnc[1] := new int[1];
	fnc[2] := new int[1];
	fnc[0][0] := 1;
	fnc[0][1] := 2;
	fnc[1][0] := -1;
	fnc[2][0] := -2;
	var sat2 := new SAT(fnc, 2);
	var isSat := sat2.isSatisfiable();
	// assert !isSat;
}
method thirdTest() {
	// A and (B or -A)
	var fnc := new array<int>[2];
	fnc[0] := new int[1];
	fnc[1] := new int[2];
	fnc[0][0] := 1;
	fnc[1][0] := 2;
	fnc[1][1] := -1;
	var sat3 := new SAT(fnc, 2);
	var isSat := sat3.isSatisfiable();
	// assert isSat;
}
method fourthTest() {
	var fnc := new array<int>[3];
	var i := 0;
	while i < 3
		invariant i <= 3
		invariant forall k | 0 <= k < i :: fnc[k].Length == 1 && fnc[k][0] == k+1
	{
		fnc[i] := new int[1];
		fnc[i][0] := i+1;
		i := i+1;
	}
	var sat4 := new SAT(fnc, 3);
	var isSat := sat4.isSatisfiable();
	//assert isSat;
}
method fifthTest() {
	// () and (A)
	var fnc := new array<int>[2];
	fnc[0] := new int[0];
	fnc[1] := new int[1];
	fnc[1][0] := 1;
	var sat5 := new SAT(fnc, 1);
	var isSat := sat5.isSatisfiable();
	// assert isSat;
}
method sixthTest() {
	var fnc := new array<int>[0];
	var sat6 := new SAT(fnc, 0);
	var isSat := sat6.isSatisfiable();
	// assert isSat;
}
method seventhTest() {
	var fnc := new array<int>[1];
	fnc[0] := new int[0];
	var sat7 := new SAT(fnc, 0);
	var isSat := sat7.isSatisfiable();
	// assert !isSat;
}

method Main() {
	firstTest();
	secondTest();
}
