
// Abstraction
class SAT {
//_______________________VARIABLES________________________________________
  var maxLenght :int ;     //taille maximal d'une solution
  var clauses : array<array<int>>;
  //TODO //probleme : tableau de clause
  //TODO

//_____________________INVARIANTS_________________________________
// SAT 
//TODO
//cree le tableau de clause ???
//initialise sol= int[maxLenght]
//return solve(sol,0)

  //Solve
  method solve(sol : array<int> , ind : int) returns (b : bool)
    requires ind >=0
    modifies sol
    decreases sol.Length - ind
  {
    if ind < sol.Length {
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
    }
    else{ //ind == maxLenght
      var check := checkSolution(sol);
      return check;
    }
  }
   method checkSolution(sol : array<int> ) returns (b : bool){
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
   
  method checkClause(sol : array<int> , cl : array<int>) returns (b : bool){
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