/*****************************************************************************
 apic.m -- the A-picture / moment characterization of the phase-1 fold states.

 Claim: on the cusp y^2 = X^N, the state
 S_j = red(tau + P_1 + ... + P_j) has U_{S_j}(z^2) = (-1)^g A_j(z) A_j(-z),
 where A_j = z^g + sum_m alpha_m z^m is the unique solution of the MOMENT SYSTEM
    sum_{m=0}^{g} alpha_m e_{(g+j)-k+m}(T_j) = 0,   k = 1, 3, ..., 2g-1,
 with T_j the multiset {t_1..t_g} + {t_1..t_j} (i <= j doubled) and e_r its
 elementary symmetric polynomials.  Consequences tested here (g <= 4, honest
 Cantor fold as reference):
   T1  A_j from the linear system reproduces the fold state U_{S_j};
   T2  detM_j and the Cramer numerators (coefficients of NA_j := detM_j*A_j)
       are SIGN-UNIFORM polynomials (skew-Schur positivity);
   T3  the fold condition at step j+1  (U_{S_j}(x_{j+1}))  and the avoidance
       U_{S_j}(0) match the determinant expressions
       (-1)^g NA_j(t)NA_j(-t)/detM_j^2  at t = t_{j+1} resp. 0;
   T4  the reduced fold-condition numerator divides NA_j(t)NA_j(-t) with
       cofactor +-2^a * monomial * detM-powers  (the dictionary).

   magma -b G:=3 apic.m
*****************************************************************************/
if not assigned G then G := "3"; end if;
g := StringToInteger(G); N := 2*g + 1;

F := FunctionField(Rationals(), g);
R<X> := PolynomialRing(F);
S<z> := PolynomialRing(F);
P := PolynomialRing(Integers(), g);
AssignNames(~P, ["t" cat IntegerToString(i) : i in [1..g]]);
AssignNames(~F, ["t" cat IntegerToString(i) : i in [1..g]]);
ts := [F.i : i in [1..g]];
xs := [ts[i]^2 : i in [1..g]]; ys := [ts[i]^N : i in [1..g]];
f := X^N;
hmF := hom<P -> F | ts>;                    // Z[t] -> F

/* ---- honest phase-1 fold (Cantor), storing states and conditions ---------- */
vF := R!0;
for i in [1..g] do
  num := R!1; den := F!1;
  for j in [1..g] do
    if j ne i then num := num*(X - xs[j]); den := den*(xs[i] - xs[j]); end if;
  end for;
  vF +:= (ys[i]/den)*num;
end for;
uF := &*[R| X - x : x in xs];
UF := uF; VF := vF;
states := [* *]; conds := [* *];            // conds[j] = <dis-value at step j, U(0) after step j>
for i in [1..g] do
  xP := xs[i]; yP := ys[i];
  t1 := Evaluate(UF, xP);
  if t1 eq 0 then
    t2 := Evaluate(VF, xP) + yP;
    Ud := Evaluate(Derivative(UF), xP);
    H := (Evaluate(Derivative(f), xP) - 2*yP*Evaluate(Derivative(VF), xP))/(2*yP*Ud);
    Uc := UF*(X - xP); Vc := VF + UF*H;
    dis := F!0;                              // step 1 is the doubling step
  else
    dis := t1;
    Uc := UF*(X - xP); Vc := VF + UF*((yP - Evaluate(VF, xP))/t1);
  end if;
  while Degree(Uc) gt g do
    cof := (Vc^2 - f) div Uc;
    Uc := cof/LeadingCoefficient(cof); Vc := (-Vc) mod Uc;
  end while;
  UF := Uc; VF := Vc;
  Append(~states, UF);
  Append(~conds, <dis, Evaluate(UF, F!0)>);
end for;

/* ---- the moment system ---------------------------------------------------- */
function MomentA(j)                          // returns detM (in P) and NA (in S, over F)
  T := ts cat ts[1..j]; Gj := g + j;
  Ez := &*[S| 1 + t*z : t in T];
  ee := func<r | (r lt 0 or r gt Gj) select F!0 else Coefficient(Ez, r)>;
  rows := [k : k in [1..2*g-1 by 2]];
  M := Matrix(F, g, g, [[ee(Gj - k + m) : m in [0..g-1]] : k in rows]);
  rhs := Vector(F, [-ee(Gj - k + g) : k in rows]);
  al := Solution(Transpose(M), rhs);         // solves M * alpha = rhs
  Aj := z^g + &+[S| al[m+1]*z^m : m in [0..g-1]];
  return Determinant(M), Aj;
end function;

/* ---- reporting helpers ---------------------------------------------------- */
function AsP(x)                              // element of F that is polynomial -> P
  n := Numerator(x); d := Denominator(x);
  error if d ne 1, "AsP: not integral";
  return P!n;
end function;

function RatToP(x, P)                        // x in F -> <n, d> integral in P
  n := Numerator(x); d := Denominator(x);
  s := LCM([Integers()| Denominator(c) : c in Coefficients(n)] cat
           [Integers()| Denominator(c) : c in Coefficients(d)]);
  return P!(s*n), P!(s*d);
end function;

function SignUniform(p)
  cs := Coefficients(p);
  return &and[c gt 0 : c in cs] or &and[c lt 0 : c in cs];
end function;

function FacStr(p)
  s := Sprintf("cont=%o", Integers()!Content(p));
  for pf in Factorization(p) do
    if #Terms(pf[1]) le 4 then s cat:= Sprintf(" (%o)^%o", pf[1], pf[2]);
    else s cat:= Sprintf(" (irr %ot d%o su=%o)^%o", #Terms(pf[1]), TotalDegree(pf[1]),
                         SignUniform(pf[1]), pf[2]);
    end if;
  end for;
  return s;
end function;

/* ---- run the tests -------------------------------------------------------- */
printf "=== apic g=%o ===\n", g;
allok := true;
for j in [0..g] do
  dM, Aj := MomentA(j);
  // T1
  if j ge 1 then
    U2 := Evaluate(states[j], z^2);
    ok := (-1)^g * Aj * Evaluate(Aj, -z) eq U2;
  else
    ok := Aj eq &*[S| z - t : t in ts];
  end if;
  if not ok then allok := false; end if;
  printf "j=%o  T1(state match): %o\n", j, ok;
  // integral objects
  dMP := AsP(dM);
  NA := [AsP(dM*Coefficient(Aj, m)) : m in [0..g]];   // coefficients of NA_j
  printf "   detM: %o terms, deg %o, sign-uniform %o, %o\n",
    #Terms(dMP), TotalDegree(dMP), SignUniform(dMP), FacStr(dMP);
  nasu := &and[SignUniform(c) : c in NA | c ne 0];
  printf "   NA_j coeffs sign-uniform: %o  contents: %o\n",
    nasu, [Integers()!Content(c) : c in NA | c ne 0];
end for;
error if not allok, "T1 FAILED";

/* ---- T3/T4: the condition dictionary -------------------------------------- */
printf "\n-- conditions vs determinant expressions --\n";
PS := PolynomialRing(P); zz := PS.1;         // z over Z[t]
for j in [1..g-1] do
  dM, Aj := MomentA(j);
  dMP := AsP(dM);
  NAz := &+[PS| AsP(dM*Coefficient(Aj, m))*zz^m : m in [0..g]];
  // T3 identity over F
  tnext := ts[j+1];
  lhsF := conds[j+1][1];                     // U_{S_j}(x_{j+1})
  rhsF := (-1)^g * Evaluate(Aj, tnext) * Evaluate(Aj, -tnext);
  printf "j=%o step-condition identity: %o\n", j, lhsF eq rhsF;
  av := conds[j][2];                         // U(0) after step j  (this is U_{S_j}(0))
  printf "j=%o avoidance identity     : %o\n", j, av eq (-1)^g*Evaluate(Aj, F!0)^2;
  // T4 dictionary on the integral side
  prod := Evaluate(NAz, P.(j+1)) * Evaluate(NAz, -P.(j+1));
  cnum, cden := RatToP(lhsF, P);
  ok, quo := IsDivisibleBy(prod, cnum);
  printf "j=%o  cond-num | NA(t)NA(-t): %o", j, ok;
  if ok then printf "   cofactor: %o\n", FacStr(quo); else printf "\n"; end if;
  printf "     cond-num: %o terms, sign-uniform %o, %o\n",
    #Terms(cnum), SignUniform(cnum), FacStr(cnum);
  printf "     cond-den: %o\n", FacStr(cden);
end for;

/* ---- T5: phase-2 conditions = in-support evaluations NA_j(t_j)NA_j(-t_j) --- */
printf "\n-- phase-2 (mirror) conditions --\n";
sigF := hom<F -> F | [ts[g + 1 - i] : i in [1..g]]>;
UF2 := states[g]; VF2 := VF;                 // continue the fold into phase 2
for k in [1..g] do
  xP := xs[k]; yP := -ys[k];
  t1 := Evaluate(UF2, xP);
  error if t1 eq 0, "phase-2 cancellation";
  Uc := UF2*(X - xP); Vc := VF2 + UF2*((yP - Evaluate(VF2, xP))/t1);
  while Degree(Uc) gt g do
    cof := (Vc^2 - f) div Uc;
    Uc := cof/LeadingCoefficient(cof); Vc := (-Vc) mod Uc;
  end while;
  UF2 := Uc; VF2 := Vc;
  j := g - k + 1;                            // honest p2.k.dis = sig(U_{S_j}(x_j))
  dM, Aj := MomentA(j);
  rhs := sigF((-1)^g * Evaluate(Aj, ts[j]) * Evaluate(Aj, -ts[j]));
  printf "p2.%o value identity (mirror): %o\n", k, t1 eq rhs;
  // integral side, unmirrored: NA_j(t_j) NA_j(-t_j) vs the reduced numerator
  dMP := AsP(dM);
  NAz := &+[PS| AsP(dM*Coefficient(Aj, m))*zz^m : m in [0..g]];
  val := (-1)^g * Evaluate(Aj, ts[j]) * Evaluate(Aj, -ts[j]);
  cnum, cden := RatToP(val, P);
  prod := Evaluate(NAz, P.j) * Evaluate(NAz, -P.j);
  ok, quo := IsDivisibleBy(prod, cnum);
  printf "   cond-num | NA(t_j)NA(-t_j): %o", ok;
  if ok then printf "   cofactor: %o\n", FacStr(quo); else printf "\n"; end if;
  printf "   cond-num: %o terms, sign-uniform %o, %o\n",
    #Terms(cnum), SignUniform(cnum), FacStr(cnum);
  printf "   cond-den: %o\n", FacStr(cden);
end for;
printf "phase-2 endpoint = (u): %o\n", UF2 eq uF;
quit;
