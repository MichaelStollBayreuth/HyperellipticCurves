/*****************************************************************************
 detcond.m -- ALL fold conditions at genus g via the moment determinants,
              NO fold, pure integral linear algebra over Z[t1..tg].

 By the moment characterization (verified against the honest Cantor fold at
 g = 3, 4 in apic.m): the phase-1 state S_j = red(tau + P_1 + ... + P_j) is
 U_{S_j}(z^2) = (-1)^g A_j(z)A_j(-z), where detM_j * A_j(z) = NA_j(z) with
 Cramer data of the g x g system
     sum_m alpha_m e_{(g+j)-k+m}(T_j) = 0   (k = 1, 3, ..., 2g-1),
 T_j = {t_1..t_g} + {t_1..t_j}.  The conditions are then VALUES:
   step condition p1.(j+1).dis = (-1)^g NA_j(t_{j+1})NA_j(-t_{j+1}) / detM_j^2,
   phase-2 (mirror) p2.(g+1-j).dis = sig of the same at t_j,
   avoidance U(0) = (-1)^g NA_j(0)^2 / detM_j^2.
 This script computes the integral objects, reduces the values to lowest
 terms, and reports sign-uniformity + integer content (+ extreme-coefficient
 contents, the char-3 probe) for every condition.

   magma -b G:=5 detcond.m
   magma -b G:=6 LOGF:=det6.log detcond.m
*****************************************************************************/
if not assigned G    then G    := "5"; end if;
if not assigned LOGF then LOGF := "";  end if;
if LOGF ne "" then SetLogFile(LOGF); end if;
g := StringToInteger(G);

P := PolynomialRing(Integers(), g);
AssignNames(~P, ["t" cat IntegerToString(i) : i in [1..g]]);
ts := [P.i : i in [1..g]];
PS := PolynomialRing(P); z := PS.1;

function SignUniform(p)
  cs := Coefficients(p);
  return &and[c gt 0 : c in cs] or &and[c lt 0 : c in cs];
end function;

procedure ReportPoly(tag, p, dg)   // sign, content, size, t1/t_g-extreme contents
  error if p eq 0, tag cat " IS ZERO";
  cont := Integers()!Content(p);
  a2 := Valuation(cont, 2);
  printf "%-24o cont=%-5o%o deg %o, %o t, sign-uniform: %o\n",
    tag, cont, cont eq 2^a2 select "" else " NOT-2-POWER", TotalDegree(p), #Terms(p),
    SignUniform(p);
  for v in [1, dg] do
    d1 := Degree(p, v); v1 := 0;
    while Coefficient(p, v, v1) eq 0 do v1 +:= 1; end while;
    printf "    t%o-range [%o..%o] top-cont=%o bot-cont=%o\n", v, v1, d1,
      Integers()!Content(Coefficient(p, v, d1)),
      Integers()!Content(Coefficient(p, v, v1));
  end for;
end procedure;

t0 := Cputime();
for j in [1..g] do
  T := ts cat ts[1..j]; Gj := g + j;
  Ez := &*[PS| 1 + t*z : t in T];
  ee := func<r | (r lt 0 or r gt Gj) select P!0 else Coefficient(Ez, r)>;
  rows := [k : k in [1..2*g-1 by 2]];
  M := Matrix(P, g, g, [[ee(Gj - k + m) : m in [0..g-1]] : k in rows]);
  rhs := [-ee(Gj - k + g) : k in rows];
  dM := Determinant(M);
  printf "== j=%o (%os) ==\n", j, Cputime(t0);
  ReportPoly(Sprintf("detM_%o", j), dM, g);
  NAc := [P|];
  for m in [0..g-1] do
    Mm := M;
    for r in [1..g] do Mm[r][m+1] := rhs[r]; end for;
    Append(~NAc, Determinant(Mm));
  end for;
  Append(~NAc, dM);
  printf "  NA coeffs: sign-uniform %o, contents %o\n",
    &and[SignUniform(c) : c in NAc | c ne 0],
    [Integers()!Content(c) : c in NAc | c ne 0];
  NAz := &+[PS| NAc[m+1]*z^m : m in [0..g]];
  dM2 := dM^2;
  evs := [<Sprintf("p1.%o.dis", j+1), j+1>, <Sprintf("p2.%o.dis(sig)", g+1-j), j>];
  if j eq g then evs := [evs[2]]; end if;   // no step g+1
  for evd in evs do
    i := evd[2];
    q := Evaluate(NAz, ts[i]) * Evaluate(NAz, -ts[i]);
    error if q eq 0, evd[1] cat " RAW VALUE ZERO";
    Gq := GCD(q, dM2);
    ok, qr := IsDivisibleBy(q, Gq); error if not ok, "quot";
    ReportPoly(evd[1], qr, g);
  end for;
  q0 := NAc[1]^2;                            // avoidance numerator NA(0)^2
  Gq0 := GCD(q0, dM2);
  ok, qr0 := IsDivisibleBy(q0, Gq0); error if not ok, "quot0";
  ReportPoly(Sprintf("p1.%o.U(0)", j), qr0, g);
  printf "  NA(0) itself: sign-uniform %o, +-square structure by construction\n",
    SignUniform(NAc[1]);
end for;
printf "total %os\n", Cputime(t0);
quit;
