/*****************************************************************************
 symfold.m -- the point-by-point fold tau + tau - tau, SYMBOLICALLY, on the
 cuspidal curve  y^2 = X^N  (N = 2g+1) with g generic points  x_i = t_i^2,
 y_i = t_i^N  over  F = Q(t_1..t_g)   (or  F = Q(q), t_i = q^{n_i}, QMODE:=1).

 Exact arithmetic -- no series, no truncation.  The fold:
   phase 1:  D := red(D + P_i),        i = 1..g   (tau -> 2 tau)
   phase 2:  D := red(D + iota(P_i)),  i = 1..g   (2 tau -> tau)
 Conditions recorded per step: the disjointness value U(x_P) (or the doubling
 pair U'(x_P), V(x_P)+y_P at step 1), and the cusp avoidance U(0).

 For each condition c = num/den the script reports
   * the INTEGER CONTENT of the primitive numerator (the char-p question:
     p | content  <=>  the condition dies identically in characteristic p),
   * the factorization of the numerator (small factors printed in full),
   * [multivariate mode] the top and bottom coefficients w.r.t. the last
     variable, factored -- the induction-on-g probe,
   * [q mode] the factorization over Q[q] with cyclotomic factors labelled.
 Sanity: endpoint identities (phase 1 = canonical red(2 tau), phase 2 = (u,v)).

   magma -b G:=3 symfold.m
   magma -b G:=4 FACT:=1 symfold.m
   magma -b G:=6 QMODE:=1 RATES:=1,2,3,4,5,6 symfold.m
*****************************************************************************/
if not assigned G     then G     := "3"; end if;
if not assigned QMODE then QMODE := "0"; end if;
if not assigned RATES then RATES := "";  end if;
if not assigned FACT  then FACT  := "1"; end if;

g := StringToInteger(G); N := 2*g + 1;
useq := QMODE eq "1"; dofact := FACT eq "1";

if useq then
  F<q> := FunctionField(Rationals());
  ns := (RATES eq "") select [1..g] else [StringToInteger(x) : x in Split(RATES, ",")];
  ts := [F| q^n : n in ns];
else
  F := FunctionField(Rationals(), g);
  AssignNames(~F, ["t" cat IntegerToString(i) : i in [1..g]]);
  ts := [F.i : i in [1..g]];
end if;
R<X> := PolynomialRing(F);
f := X^N;
xs := [ts[i]^2 : i in [1..g]];
ys := [ts[i]^N : i in [1..g]];

function Lagrange(xs, vals)
  v := R!0;
  for i in [1..#xs] do
    num := R!1; den := F!1;
    for j in [1..#xs] do
      if j ne i then num := num*(X - xs[j]); den := den*(xs[i]-xs[j]); end if;  end for;
    v := v + (vals[i]/den)*num;  end for;
  return v;
end function;

function ExactQuo(a, b, msg)
  qq, r := Quotrem(a, b); error if r ne 0, msg; return qq;
end function;

/* ---------- the fold ------------------------------------------------------- */
conds := [* *]; shape := [];

procedure AddPoint(~U, ~V, xP, yP, tag, ~conds, ~shape)
  t1 := Evaluate(U, xP);
  if t1 eq 0 then
    t2 := Evaluate(V, xP) + yP;
    error if t2 eq 0, tag cat ": unexpected cancellation";
    Ud := Evaluate(Derivative(U), xP);
    Append(~conds, <tag cat ".dbl_U'(xP)", Ud>);
    Append(~conds, <tag cat ".dbl_V(xP)+yP", t2>);
    H := (Evaluate(Derivative(f), xP) - 2*yP*Evaluate(Derivative(V), xP)) / (2*yP*Ud);
    Ucomp := U*(X - xP);  Vcomp := V + U*H;
    Append(~shape, "DBL");
  else
    Append(~conds, <tag cat ".dis_U(xP)", t1>);
    Ucomp := U*(X - xP);
    Vcomp := V + U*((yP - Evaluate(V, xP))/t1);
    Append(~shape, "DIS");
  end if;
  error if (Vcomp^2 - f) mod Ucomp ne 0, tag cat ": divisibility fails";
  while Degree(Ucomp) gt g do
    cof := ExactQuo(Vcomp^2 - f, Ucomp, tag cat ": cofactor");
    Unew := cof/LeadingCoefficient(cof);
    Vnew := (-Vcomp) mod Unew;
    Ucomp := Unew; Vcomp := Vnew;
  end while;
  U := Ucomp; V := Vcomp;
end procedure;

u := &*[X - x : x in xs];  v := Lagrange(xs, ys);
U := u; V := v;
inters := [* *];
printf "=== g=%o N=%o %o ===\n", g, N,
  useq select Sprintf("q-mode rates=%o", ns) else "full symbolic";
for ph in [1..2] do
  for i in [1..g] do
    tag := Sprintf("p%o.%o", ph, i);
    yy := ph eq 1 select ys[i] else -ys[i];
    AddPoint(~U, ~V, xs[i], yy, tag, ~conds, ~shape);
    Append(~conds, <tag cat ".U(0)", Evaluate(U, F!0)>);
    Append(~inters, <tag, U, V>);
    printf "[%o %os]\n", tag, Cputime();
  end for;
  printf "[phase %o done]\n", ph;
end for;
printf "shape: %o\n", shape;

/* ---------- sanity: endpoints --------------------------------------------- */
w  := ExactQuo(v^2 - f, u, "u | v^2 - f");
c2 := Lagrange(xs, [1/(2*ys[i]) : i in [1..g]]);
vt := v - u*((c2*w) mod u);
error if (vt^2 - f) mod u^2 ne 0, "doubleV check fails";
Us := u^2; Vs := vt;
while Degree(Us) gt g do
  cof := ExactQuo(Vs^2 - f, Us, "std chain cofactor");
  Us := cof/LeadingCoefficient(cof);  Vs := (-Vs) mod Us;
end while;
printf "phase-1 endpoint = canonical red(2tau): %o\n",
  (inters[g][2] eq Us) and (inters[g][3] eq Vs);
printf "phase-2 endpoint = (u, v)             : %o\n", (U eq u) and (V eq v);
i21 := [i : i in [1..#conds] | conds[i][1] eq "p2.1.dis_U(xP)"][1];
printf "old bez3 = prod_i U2(x_i): p2.1 value is its first factor: %o\n",
  Evaluate(Us, xs[1]) eq conds[i21][2];

/* ---------- reporting ------------------------------------------------------ */
function RatContent(p)          // rational content of a poly over Q
  cs := Coefficients(p);
  return GCD([Integers()| Numerator(c) : c in cs])
       / LCM([Integers()| Denominator(c) : c in cs]);
end function;

function FStr(r)                // factored rational as string
  if r eq 0 then return "0"; end if;
  n := Numerator(r); d := Denominator(r); s := (r lt 0) select "-" else "";
  fn := Factorization(AbsoluteValue(Integers()!n)); fd := Factorization(Integers()!d);
  ns := (#fn eq 0) select "1" else &cat[Sprintf("%o^%o.", p[1], p[2]) : p in fn];
  ds := (#fd eq 0) select "" else "/" cat &cat[Sprintf("%o^%o.", p[1], p[2]) : p in fd];
  return s cat ns cat ds;
end function;

cyclab := function(h)           // label Phi_n for cyclotomic h in Q[q]
  d := Degree(h);
  if d eq 0 then return ""; end if;
  for n in [1..Min(4*d^2 + 6, 600)] do
    if EulerPhi(n) eq d and IsDivisibleBy(Parent(h).1^n - 1, h) then
      return Sprintf("[Phi_%o]", n);
    end if;
  end for;
  return "";
end function;

printf "\n-- conditions: content and factor structure --\n";
for c in conds do
  val := c[2];
  error if val eq 0, c[1] cat " IS ZERO";
  n := Numerator(val);
  cont := RatContent(n);
  printf "%-16o content=%-12o", c[1], FStr(cont);
  if useq then
    n0 := n / cont;
    v0 := Valuation(n0);  n1 := n0 div Parent(n0).1^v0;
    printf " q^%o * deg %o : ", v0, Degree(n1);
    if dofact then
      for pf in Factorization(n1) do
        lbl := cyclab(pf[1]);
        if lbl ne "" then printf "%o^%o ", lbl, pf[2];
        elif Degree(pf[1]) le 8 then printf "(%o)^%o ", pf[1], pf[2];
        else printf "(irr deg %o, %o terms)^%o ", Degree(pf[1]), #Terms(pf[1]), pf[2];
        end if;
      end for;
    end if;
    printf "\n";
  else
    printf " deg %o, %o terms", TotalDegree(n), #Terms(n);
    if dofact and #Terms(n) le 4000 then
      printf " : ";
      for pf in Factorization(n) do
        if #Terms(pf[1]) le 6 then printf "(%o)^%o ", pf[1], pf[2];
        else printf "(irr deg %o, %o terms)^%o ", TotalDegree(pf[1]), #Terms(pf[1]), pf[2];
        end if;
      end for;
    end if;
    printf "\n";
    // induction probe: top and bottom coefficient w.r.t. the last variable
    dg := Degree(n, g);  vg := 0;
    while Coefficient(n, g, vg) eq 0 do vg +:= 1; end while;
    top := Coefficient(n, g, dg);  bot := Coefficient(n, g, vg);
    printf "    t%o-range [%o..%o]  top: cont=%o deg %o, %o terms   bot: cont=%o deg %o, %o terms\n",
      g, vg, dg, FStr(RatContent(top)), TotalDegree(top), #Terms(top),
      FStr(RatContent(bot)), TotalDegree(bot), #Terms(bot);
  end if;
end for;
printf "ALL CONDITIONS NONZERO (exact): true\n";

/* ---------- structural probes: positivity and squares ---------------------- */
printf "\n-- probes --\n";
allpos := true; allsq := true;
for c in conds do
  n := Numerator(c[2]);
  cs := Coefficients(n);
  pos := &and[cc gt 0 : cc in cs] or &and[cc lt 0 : cc in cs];
  if not pos then allpos := false; printf "  %-16o NOT sign-uniform\n", c[1]; end if;
end for;
printf "all condition numerators sign-uniform (all coeffs same sign): %o\n", allpos;
for c in conds do
  if Position(c[1], "U(0)") ne 0 then
    v := c[2];
    if not (IsSquare(v) or IsSquare(-v)) then
      allsq := false; printf "  %-16o U(0) NOT +-square\n", c[1];
    end if;
  end if;
end for;
printf "all avoidance values U(0) are +-squares in F: %o\n", allsq;
quit;
