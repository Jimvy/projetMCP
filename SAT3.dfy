/**
 * Un solveur SAT très très basique qui ne fait pas de CDCL, même pas de DPLL. Juste un bon gros DFS qui cherche
 * trouver un assignment ou exhauster toutes les possibilites.
 */
module SAT {

 /*-------------------------------------------------------------------------------------------------------------
  *  Les types de base:
  * ####################
  *-------------------------------------------------------------------------------------------------------------
  * 1. Bool
  * ------------
  * Dans un solveur SAT, bool est le type des valeurs basiques qui sont assignées aux variables (et literaux).
  * C'est pourquoi le type Bool d'un solveur SAT ne correspond pas tout à fait au type booleen tel qu'il existe
  * dans la plupart des langages de programmation. En effet, il s'agit d'une logique tri-valuée puisque chaque
  * variable du problème peut-être soit assignée à VRAI, soit à FALSE, soit ne PAS ETRE ASSIGNEE DU TOUT
  */
  datatype Bool = Undefined | True | False

  // Donne la négation d'une valeur booléenne (dans une tri-valued logic)
  function method not(b: Bool) : Bool {
      match b {
        case True => False
        case False => True
        case Undefined => Undefined
      }
  }

 /* 2. Variable
  * -------------
  * Une variable est l'identifiant d'une proposition atomique à laquelle il faut associer une valeur de vérité
  * (Bool).
  */
  type Var = nat

 /* 3. Literal
  * -----------
  * Un literal est soit une variable, soit la négation d'une variable.
  */
  datatype Sign = Positive | Negative
  datatype  Lit = lit(v: Var, s: Sign)

 /* 4. Valuation
  * ------------
  * Une valuation est un mapping qui associe une valeur de vérité (Bool) à chacune des propositions atomiques (Var)
  * du problème. En particulier, une solution au problème est une valuation dans laquelle toutes les variables
  * sont associées à une valeur soit True, soit False (donc pas de Undefined) et qui ne viole aucune des clauses
  * du problème.
  */
  type Valuation = seq<Bool>

  // Retourne la valeur d'un literal étant donné une valuation
  function value_of(l: Lit, v: Valuation) : Bool 
      requires 0 <= l.v < |v|
  {
      if l.s == Negative then not(v[l.v])
      else                    v[l.v]
  }

  // SPEC: Renvoie vrai ssi aucune variable n'est assignée dans la valuation
  predicate empty(v: Valuation) 
  {
      forall i:nat | 0 <= i < |v| :: v[i].Undefined?
  }

  // Renvoie une valuation par défaut (pour un nombre donné de variables)
  method default_valuation(size: nat) returns (result: array<Bool>) 
    ensures result.Length == size
    ensures empty(result[..])
    ensures fresh(result)
  {
      var valuation := new Bool[size];
      var i         := 0;
      
      while i < size 
        invariant 0 <= i <= size && forall j:nat | 0 <= j < i :: valuation[j].Undefined?
        decreases size-i
     {
        valuation[i] := Undefined;
        i            := i + 1;
     }
     return valuation;
  }

  // SPEC: Renvoie true iff la valuation est complète (toutes les variables ont obtenu une valeur)
  predicate complete(v: Valuation) 
      ensures complete(v) <==> forall x: Var | x < |v| :: (v[x].True? || v[x].False?)
  {
      forall x: Var | x < |v| :: v[x] != Undefined
  }


 /* 5. Instance et Clause
  * ----------------------
  * Une instance de problème SAT est toujours formulée sous forme normale conjonctive. C'est à dire que le problème
  * complet est modélisé comme une conjonction (AND) de clauses (contraintes). Les clauses étant elle-même des
  * disjonctions (OR) de litéraux.
  *
  * .. note::
  *    Il est important de constater qu'en vertu des propriétés des opérateurs AND et OR, une *instance vide*
  *    (un ensemble qui ne contient aucune clause) est SATISFAISABLE par définition. Tandisqu'une *clause vide*
  *    (un ensemble qui ne contient aucun literal) est FALSIFIEE par définition.
  */
  type Clause   = seq<Lit>
  type Instance = seq<Clause>

  // renvoie true iff toutes les variables utilisées pour formuler 'c' obtiennent une valeur via 'v'
  predicate clause_agree_on_size(c: Clause, v: Valuation) {
      forall l:Lit | l in c :: 0 <= l.v < |v|
  }

  // renvoie true iff toutes les variables utilisées pour formuler le problème obtiennent une valeur via 'v'
  predicate instance_agree_on_size(i: Instance, v: Valuation) {
      forall c:Clause | c in i :: clause_agree_on_size(c, v)
  }

  // SPEC : Renvoie vrai ssi la clause 'c' est violée selon la valuation 'v' donnée.
  predicate falsified(c: Clause, v: Valuation) 
    requires clause_agree_on_size(c, v)
  {
      forall l: Lit | l in c :: value_of(l, v).False?
  }
  
  // SPEC: Renvoie true ssi la valuation 'v' est en conflit avec l'ensemble de clause qui composent l'instance
  predicate conflicting(i: Instance, v: Valuation) 
    requires instance_agree_on_size(i, v)
  {
      exists c: Clause | c in i :: falsified(c, v)
  }

 /*-------------------------------------------------------------------------------------------------------------
  *  Le solveur SAT:
  * ##################
  * Dans sa version la plus simple (celle que vous devez implémenter), un solveur SAT est un objet qui étant
  * donné une instance (sous forme CNF) cherche à savoir s'il existe une valuation qui soit consistante avec 
  * toutes les clauses du problème. C'est à dire une valuation qui ne viole aucune des clauses. 
  * 
  * Pour ce faire, un solveur SAT utilise une recherche complète type depth-first-search afin de décider de 
  * l'existence ou non d'une solution.
  *
  *
  * Exemple:
  * ~~~~~~~~~
  * Si on a la clause (a, b, c) et que notre valuation courante est (a->False, b->False, c->Undefined) alors
  * la propagation unitaire dit que la variable c doit se voir affecter la valeur True. Sans quoi notre clause
  * (a, b, c) serait falsifiée.
  *-------------------------------------------------------------------------------------------------------------*/

  // toutes les variables sont dans le range 0..nb_vars-1
  predicate all_literals_in_range(nb_vars: nat, problem: Instance) 
      // ensures forall v: Valuation | |v| >= nb_vars :: instance_agree_on_size(problem, v)
  {
      forall c : Clause | c in problem :: forall l : Lit | l in c :: 0 <= l.v < nb_vars
  }

  // SPEC: a et b ont la même valeur pour leurs n premières entrées.
  predicate prefix(n: nat, a: Valuation, b: Valuation)
      requires n <= |a|
      ensures prefix(n, a, b) ==> (|a| == |b| && a[..n] == b[..n])
  {
      |a| == |b| && ( forall k: nat | k < n :: a[k] == b[k] )
  }

	// SPEC: a et b ont la même valeur pour leurs n premières entrées.
  predicate prefixComplete(n: nat, a: Valuation, b: Valuation)
      requires n <= |a|
      ensures prefix(n, a, b) ==> (|a| == |b| && a[..n] == b[..n])
  {
      |a| == |b| && complete(b) && ( forall k: nat | k < n :: a[k] == b[k] )
  }

  // SPEC: b est une valuation complète, et a a la même valeur que b pour toutes les entrées qui ne sont pas Undefined.
  predicate compatible(a: Valuation, b: Valuation)
  {
      |a| == |b| && complete(b) && ( forall i | 0 <= i < |a| :: a[i] != Undefined ==> a[i] == b[i] )
  }

  // SPEC: teste si valuation est une solution pour problem
  predicate solution(valuation: Valuation, problem: Instance)
      requires instance_agree_on_size(problem, valuation)
  {
      complete(valuation) && !conflicting(problem, valuation)
  }

  class SatSolver {
      var nb_vars  : nat
      var problem  : Instance
      var valuation: array<Bool>
      var debug    : bool

    constructor (n: nat, i: Instance, debug_: bool)
        requires all_literals_in_range(n, i)
        ensures  this.nb_vars          == n
        ensures  this.problem          == i
        ensures  ok()
        ensures  fresh(valuation)
        ensures  empty(this.valuation[..])
        //lol Todo
    {
        nb_vars   := n;
        problem   := i;
        debug     := debug_;
        new;
        valuation := default_valuation(n);
    }

    predicate ok()
        reads this, valuation
    {
        valuation.Length == nb_vars
        && instance_agree_on_size(problem, valuation[..])
    }


    method value(l: Lit) returns (v: Bool)
        requires ok()
        requires 0 <= l.v < valuation.Length
        ensures v == value_of(l, valuation[..]);
    {
        match l.s {
            case Positive => return valuation[l.v];
            case Negative => return not(valuation[l.v]);
        }
    }

    // IMPLEM: Renvoie vrai ssi la clause 'c' est violée selon la valuation 'v' donnée.
    method is_falsified(c: Clause) returns (result : bool) 
        requires ok()
        requires clause_agree_on_size(c, valuation[..])
        // TODO ok
        ensures result==falsified(c, this.valuation[..])
    {
        var i := 0; 
        while i < |c|
          invariant i <= |c|
          invariant ok()
          invariant clause_agree_on_size(c, valuation[..])

          invariant forall k:nat | k<i :: value_of(c[k],valuation[..]) == False
          // TODO ok
          decreases |c| - i
        {
            var val := value(c[i]);
            if val != False {
                return false;
            }
            i := i + 1;
        }
        return true;
    }

    // IMPLEM: Renvoie true ssi la valuation 'v' est en conflit avec l'ensemble de clause qui composent l'instance
    method is_conflicting() returns (result: bool)
        requires ok()
        //requires instance_agree_on_size(this.problem, this.valuation[..])
        ensures result == conflicting(this.problem, this.valuation[..])
        // TODO ok
    {
        var k := 0;
        while k < |problem| 
            invariant ok()
            invariant k <= |problem|
            // TODO ok
            invariant forall i: nat | i < k :: !falsified(problem[i], valuation[..])
            decreases |problem| - k
        {
            var conflict_found := is_falsified(problem[k]);
            if conflict_found {
                return true;
            }
            k := k + 1;
        }
  
        return false;
    }

    // IMPLEM: Renvoie true iff la valuation est complète (toutes les variables ont obtenu une valeur)
    method is_complete() returns (result: bool) 
        requires ok()
        //TODO ok

        ensures result==complete(this.valuation[..])
    {
        var i := 0;
        while i < valuation.Length 
          invariant ok()
          invariant 0 <= i <= valuation.Length
          invariant forall k:nat | k < i :: this.valuation[k] != Undefined
          // TODO
          decreases valuation.Length - i
        {
          if valuation[i].Undefined? {
              return false;
          }
          i := i + 1;
        }
  
        return true;
    }

    method solve() returns (result: bool) 
        requires ok()
        ensures  ok()
        // La post à prouver:
        ensures  result <==> exists v: Valuation | |v| == nb_vars :: solution(v, problem)
        //ensures  result <==> at_solution()
        modifies valuation
    {
        forall (i | 0 <= i < nb_vars) { valuation[i] := Undefined; }
        result := search(0);
    }

    method search(decision: nat) returns (result: bool) 
        requires  ok()
        requires  0 <= decision <= nb_vars
        // TODO (more requires)
        requires instance_agree_on_size(this.problem, valuation[..])
        requires complete(valuation[..decision])
        decreases nb_vars - decision
        modifies  valuation

        ensures ok()
        ensures complete(valuation[..decision])
        // TODO (more ensures)
				ensures exists sol: Valuation :: (|sol| == |old(valuation[..])|) && complete(sol) && prefixComplete(decision, old(valuation[..]), sol)
        ensures result <==> exists sol: Valuation | (|sol| == |old(valuation[..])|) && complete(sol) && prefixComplete(decision, old(valuation[..]), sol) :: solution(sol, problem)
				ensures prefix(decision, valuation[..], old(valuation[..]))
    {
        if (debug) {
            print_valuation();
        }

        // Si on a assigné toutes les variables (potentiellement, aucune), on doit quand même vérifier
        // qu'on a trouvé une solution réelle. (Cas du problème avec zero variables, mais une clause vide)
        if decision == nb_vars {
            result := solution_found();
            return;
        }

        // (BONUS, plus difficile à prouver is_conflicting())
        // Shortcut pour quand même détecter qu'il y a un conflit avant d'avoir assigné toutes les variables
        //var conflict_ := is_conflicting();
        //if conflict_ {
        //    return false;
        //}

        // 1. Try true
        valuation[decision] := True;
        var finished_ := search(decision + 1);
				assert finished_ <==> exists sol: Valuation | (|sol|==|valuation[..]|) && complete(sol) && prefix(decision+1, valuation[..], sol) :: solution(sol, problem);
        if finished_ {
					  //assert (exists sol: Valuation | valuation[decision]==True && (|sol|==|valuation[..]|) && /*valuation[decision]==True &&*/ complete(sol) && prefix(decision+1, valuation[..], sol) :: solution(sol, problem));
            return true;
        }
				assert !(exists sol: Valuation | (|sol|==|valuation[..]|) && complete(sol) && prefix(decision+1, valuation[..], sol) :: solution(sol, problem));
				assert !(exists sol: Valuation | (|sol|==|valuation[..]|) && sol[decision]==True && complete(sol) && prefix(decision+1, valuation[..], sol) :: solution(sol, problem));
				//assert !(exists sol: Valuation | (|sol|==|valuation[..]|) && sol[decision]==True && complete(sol) && prefix(decision, valuation[..], sol) :: solution(sol, problem));

        // 2. Try false
        valuation[decision] := False;
        finished_ := search(decision + 1);
        if finished_ {
					//assert (exists sol: Valuation | (|sol|==|valuation[..]|) && complete(sol) && prefix(decision+1, valuation[..], sol) :: solution(sol, problem));
            return true;
        }
				//assert exists sol: Valuation :: (|sol|==|valuation[..]|) && sol[decision]==False && complete(sol) && prefix(decision, valuation[..], sol) ;
				//assert !(exists sol: Valuation | (|sol|==|valuation[..]|) && sol[decision]==False && complete(sol) && prefix(decision+1, valuation[..], sol) :: solution(sol, problem));
				//assert !(exists sol: Valuation | (|sol|==|valuation[..]|) && (sol[decision]==True || sol[decision]==False)  && complete(sol) && prefix(decision+1, valuation[..], sol) :: solution(sol, problem));
				//assert !(exists sol: Valuation | (|sol|==|valuation[..]|) && complete(sol) && prefix(decision+1, valuation[..], sol) :: solution(sol, problem));

        // 3. Backtrack
				//assert ! (exists sol: Valuation | valuation[decision]==True && (|sol|==|valuation[..]|) && complete(sol) && prefix(decision+1, valuation[..], sol) :: solution(sol, problem)) && !(exists sol: Valuation | valuation[decision]==False && (|sol|==|valuation[..]|) && complete(sol) && prefix(decision+1, valuation[..], sol) :: solution(sol, problem));
				//assert ! (exists sol: Valuation | sol[decision]==True && (|sol|==|valuation[..]|) && complete(sol) && prefix(decision+1, valuation[..], sol) :: solution(sol, problem)) && !(exists sol: Valuation | sol[decision]==False && (|sol|==|valuation[..]|) && complete(sol) && prefix(decision+1, valuation[..], sol) :: solution(sol, problem));
				//assert !((exists sol: Valuation | valuation[decision]==True && (|sol|==|valuation[..]|) && complete(sol) && prefix(decision+1, valuation[..], sol) :: solution(sol, problem)) || (exists sol: Valuation | valuation[decision]==False && (|sol|==|valuation[..]|) && complete(sol) && prefix(decision+1, valuation[..], sol) :: solution(sol, problem))) <==> !(exists sol: Valuation | (|sol|==|valuation[..]|) && complete(sol) && prefix(decision+1, valuation[..], sol) :: solution(sol, problem));
				//assert !((exists sol: Valuation | (valuation[decision]==True || valuation[decision]==False || valuation[decision]==Undefined ) && (|sol|==|valuation[..]|) && complete(sol) && prefix(decision+1, valuation[..], sol) :: solution(sol, problem)));
				//assert !(exists sol: Valuation | valuation[decision] == Undefined && (|sol|==|valuation[..]|) && complete(sol) && prefix(decision+1, valuation[..], sol) :: solution(sol, problem));
				//assert !((exists sol: Valuation | (sol[decision]==True || sol[decision]==False || sol[decision]==Undefined ) && (|sol|==|valuation[..]|) && complete(sol) && prefix(decision+1, valuation[..], sol) :: solution(sol, problem)));

        valuation[decision] := Undefined;

				//assert !(exists sol: Valuation | (|sol|==|valuation[..]|) && complete(sol) && prefix(decision, valuation[..], sol) :: solution(sol, problem));
        return false;
    }

    // SPEC: Renvoie true ssi on a trouvé une solution
    predicate at_solution() 
        requires instance_agree_on_size(problem, valuation[..])
        requires valuation.Length == nb_vars
        reads this
        reads this.valuation
        ensures at_solution() <==> solution(valuation[..], problem)
    {
        solution(valuation[..], problem)
    }

    // IMPLEM: Renvoie true ssi on a trouvé une solution
    method solution_found() returns (result: bool)
        requires ok()
        // TODO ok
        ensures result <==> solution(valuation[..], problem)
        ensures ok()
    {
        var complete_ := is_complete();
        if !complete_ {
            return false;
        }
        var conflict_ := is_conflicting();
        if conflict_ {
            return false;
        }
        return true;
    }

    method print_valuation()
        requires instance_agree_on_size(problem, valuation[..])
        requires  nb_vars == valuation.Length
    {
        print "[";
        var i := 0;
        while i < nb_vars 
            decreases nb_vars - i
            invariant 0 <= i <= nb_vars
        {
            if i > 0 { print ", "; }
            match valuation[i] {
                case True      => print "True";
                case False     => print "False";
                case Undefined => print "Undefined";
            }
            i := i+1;
        }
        print "]\n";
    }
  }

method print_problem (p: Instance) {
    print "p cnf 4 ", |p|, "\n";
    var c := 0;
    while c < |p| 
        decreases |p| - c
    {
        var l := 0;
        while l < |p[c]| 
            decreases |p[c]| - l
        {
            if p[c][l].s == Negative {
                print "-";
            }
            print p[c][l].v + 1, " ";
            l := l + 1;
        }
        print "0\n";
        c := c + 1;
    }
}
    

method solve(p: Instance) 
    requires all_literals_in_range(4, p);
{
    print "\n";
    print_problem(p);
    var solver := new SatSolver(4, p, false);
    var found := solver.solve();
    if (found) {
        print "SAT: ";
        solver.print_valuation();
    } else {
        print "UNSAT\n";
    }
}

method Main() {
    var a, a_ := lit(0, Positive), lit(0, Negative);
    var b, b_ := lit(1, Positive), lit(1, Negative);
    var c, c_ := lit(2, Positive), lit(2, Negative);
    var d, d_ := lit(3, Positive), lit(3, Negative);

    solve([[a, b, c_], [c, d_], [a_, b], [a_, c_], [a_], [b_]]);
    solve([[a], [a_]]);
    solve([
            [a,b,c,d],
            [a,b,c,d_],
            [a,b,c_,d],
            [a,b,c_,d_],
            //[a,b_,c,d], <- the solution
            [a,b_,c,d_],
            [a,b_,c_,d],
            [a,b_,c_,d_],
            [a_,b,c,d],
            [a_,b,c,d_],
            [a_,b,c_,d],
            [a_,b,c_,d_],
            [a_,b_,c,d],
            [a_,b_,c,d_],
            [a_,b_,c_,d],
            [a_,b_,c_,d_]
    ]);
}
}
