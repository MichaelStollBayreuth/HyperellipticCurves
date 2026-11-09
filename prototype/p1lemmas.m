/*****************************************************************************
 p1lemmas.m -- verify the exact lemma chain of the moment theorem (blueprint
 thm:cusp-moment).

 State: (U, V) the Mumford pair of S_j on y^2 = X^N (N = 2g+1), plus the
 base-rational A_j defined by the fold recursion:
   A_0 = prod (z - t_i);
   compose: A_c = A_j (z - t_{j+1});
   reduce : A_{j+1} = (-1)^g C_c(-z),  C_c = (z^N - V_c(z^2)) / A_c(z).
 Lemmas (all EXACT except L4 which is mod z^{2g+1}):
   L1  A_c(z) | z^N - V_c(z^2)
   L2  U_new(z^2) = (-1)^g A_new(z) A_new(-z)  and  A_new is monic of degree g
   L3  A_new(z) A_c(-z) - A_new(-z) A_c(z) = (-1)^(g+1) 2 z^N   (sign checked!)
   L4  A_j(z) d_j(-z) = A_j(-z) d_j(z) mod z^(2g+1),  d_j = prod (t_i - z)^{e_i}
   L5  A_j solves the moment system (equivalent formulation of L4)

   magma -b G:=3 p1lemmas.m
*****************************************************************************/
if not assigned G then G := "3"; end if;
g := StringToInteger(G); N := 2*g + 1;

F := FunctionField(Rationals(), g);
R<X> := PolynomialRing(F);
S<z> := PolynomialRing(F);
ts := [F.i : i in [1..g]];
xs := [ts[i]^2 : i in [1..g]]; ys := [ts[i]^N : i in [1..g]];
f := X^N;

vF := R!0;
for i in [1..g] do
  num := R!1; den := F!1;
  for j in [1..g] do
    if j ne i then num := num*(X - xs[j]); den := den*(xs[i] - xs[j]); end if;
  end for;
  vF +:= (ys[i]/den)*num;
end for;
U := &*[R| X - x : x in xs]; V := vF;
A := &*[S| z - t : t in ts];
dd := &*[S| t - z : t in ts];                 // d_0

function OddTrunc(p, m)                       // odd part of p mod z^m
  return &+[S| Coefficient(p, k)*Parent(p).1^k : k in [1..Min(Degree(p), m-1) by 2]];
end function;

printf "=== p1lemmas g=%o ===\n", g;
printf "L4 base (exact): %o\n",
  A*Evaluate(dd, -z) eq Evaluate(A, -z)*dd;   // j = 0: exact identity
allok := true;
for i in [1..g] do
  xP := xs[i]; yP := ys[i]; t := ts[i];
  t1 := Evaluate(U, xP);
  if t1 eq 0 then
    Ud := Evaluate(Derivative(U), xP);
    H := (Evaluate(Derivative(f), xP) - 2*yP*Evaluate(Derivative(V), xP))/(2*yP*Ud);
  else
    H := (yP - Evaluate(V, xP))/t1;
  end if;
  Uc := U*(X - xP); Vc := V + U*H;
  Ac := A*(z - t);
  // L1
  Ynum := z^N - Evaluate(Vc, z^2);
  ok1, Cc := IsDivisibleBy(Ynum, Ac);
  printf "step %o: L1 (A_c | z^N - V_c(z^2)): %o\n", i, ok1;
  allok and:= ok1;
  // Cantor reduce
  cof := (Vc^2 - f) div Uc;
  Unew := cof/LeadingCoefficient(cof); Vnew := (-Vc) mod Unew;
  Anew := (-1)^g * Evaluate(Cc, -z);
  // L2
  ok2 := (Evaluate(Unew, z^2) eq (-1)^g * Anew * Evaluate(Anew, -z))
         and (LeadingCoefficient(Anew) eq 1) and (Degree(Anew) eq g);
  printf "step %o: L2 (U_new via A_new, monic deg g): %o\n", i, ok2;
  allok and:= ok2;
  // L3 exact
  lhs := Anew*Evaluate(Ac, -z) - Evaluate(Anew, -z)*Ac;
  ok3 := lhs eq (-1)^(g+1)*2*z^N;
  printf "step %o: L3 (exact, = (-1)^(g+1) 2 z^N): %o\n", i, ok3;
  allok and:= ok3;
  // advance and check L4
  U := Unew; V := Vnew; A := Anew;
  dd := dd*(t - z);
  G4 := A*Evaluate(dd, -z) - Evaluate(A, -z)*dd;
  ok4 := &and[Coefficient(G4, k) eq 0 : k in [0..2*g]];
  printf "step %o: L4 (master congruence mod z^%o): %o\n", i, N, ok4;
  allok and:= ok4;
  // avoidance = the invertibility used in L4's reduce step
  printf "step %o: A_j(0) <> 0 (avoidance/invertibility): %o\n", i, Evaluate(A, F!0) ne 0;
end for;
printf "ALL LEMMAS VERIFIED: %o\n", allok;
quit;
