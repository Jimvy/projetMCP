
//datatype Solution = array<int>
function method abs(x: int): int {
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
	predicate okN()
		reads this
	{
		n >= 0
	}
	predicate ok()
		reads this, clauses, clauses[..]
	{
		okFNC(clauses, n) && n >= 0
	}
	// Garantit que les variables de 1 à ind compris ont de bonnes valeurs. Notamment, okSol(sol, 0) ne spécifie aucune variable, okSol(sol, 1) spécifie 1 variable, okSol(sol, n) spécifie toutes les variables.
	predicate okSol(sol: array<int>, ind: int)
		reads this, sol
		requires okN()
		requires 0 <= ind <= n
	{
		sol.Length >= n+1 && sol[0] == 0
			&& forall k | 1 <= k <= ind :: (sol[k] == k || sol[k] == -k)
			// && forall l | ind < l <= n :: sol[l] == 0
			// FIXME comprendre pourquoi le rajout de cette condition fait tout foirer.
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
		/*assume n == 4;
		var tab := new int[5];
		tab[0], tab[1], tab[2], tab[3], tab[4] := 0, -1, 2, 3, -4;
		assert okSol(tab, 4);*/
		var sol := new int[n+1]; // L'élément 0 est ignoré.
		var i := 0;
		while i < sol.Length
			invariant 0 <= i <= sol.Length
			invariant forall k | 0 <= k < i :: sol[k] == 0
		{
			sol[i] := 0;
			i := i+1;
		}
		assert okSol(sol, 0); // toujours vraie
		/*assume n > 0;
		sol[1] := 1;
		assert okSol(sol, 1);*/
		b := solve(sol, 1);
	}

	method solve(sol: array<int>, ind: int) returns (b : bool)
		requires 1 <= ind <= n+1
		requires sol.Length >= n+1
		requires okSol(sol, ind-1)
		ensures okSol(sol, ind-1)
		requires ok()
		ensures ok()
		modifies sol
		decreases sol.Length - ind
  {
		assert okSol(sol, ind-1);
		/*assume ind == n - 2;
		assume ind == 2;
		assume n == 4;
		assume sol.Length == 5;
		assert okSol(sol, ind-1);
		assert sol.Length >= n+1;
		assert sol[0]==0;
		assume ind <= n;
		assert forall k | 1 <= k <= (ind-1) :: (sol[k] == k || sol[k] == -k);*/
		//assert forall l | ind+1 <= l <= n :: sol[l] == 0;
		/*forall (k | ind <= k <= n) {
			assert sol[k] == 0;
		}*/
		/*var k := ind;
		while k <= n
			invariant ind <= k <= n+1
		{
			assert sol[k] == 0;
			k := k+1;
		}*/
    if ind <= n {
      assert okSol(sol, ind-1);
      sol[ind] := ind;
      assert okSol(sol, ind);
      var solved := solve(sol, ind + 1);
      assert okSol(sol, ind);
      if solved {
        b := solved;
      } else {
        assert okSol(sol, ind);
        sol[ind] := -ind;
        assert okSol(sol, ind);
        b := solve(sol,ind + 1);
      }
        assert okSol(sol, ind);
        sol[ind] := 0;
        assert okSol(sol, ind-1);
    } else { //ind == maxLenght
      assert okSol(sol, n);
      var check := checkSolution(sol);
      assert okSol(sol, n);
      return check;
    }
  }

	method checkSolution(sol : array<int>) returns (b : bool)
		requires ok() // n >= 0
		requires n >= 0
		requires okSol(sol, n)
  {
    var i := 0;
    while i < clauses.Length
      invariant 0 <= i <= clauses.Length
      decreases clauses.Length - i;
    {
      var check := checkClause(sol , clauses[i]);
      if !check 
      {
        return false;
      }
      i := i+1;
    }
    return true;
  }

	method checkClause(sol : array<int> , clause : array<int>) returns (b : bool)
		requires okN() // n >= 0 ; on n'a pas besoin de toutes les autres clauses
		requires okClause(clause, n)
		requires okSol(sol, n);
  {
    var i := 0;
    while i < clause.Length
      invariant 0 <= i <= clause.Length
      decreases clause.Length - i;
    {
      var elem := clause[i];
      var ind := abs(elem);
      if sol[ind] == elem {
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
