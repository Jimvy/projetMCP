// Abstraction
class SAT {
//_______________________VARIABLES________________________________________
  var maxLenght :int ;     //taille maximal d'une solution
  //TODO //probleme : tableau de clause
  //TODO

//_____________________INVARIANTS_________________________________

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
     //TODO
     return true ;
   }
  
}