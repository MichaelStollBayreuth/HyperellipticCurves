/*****************************************************************************
 p34atoms.m -- the condition ATOMS are the single Schur
 values  s_Lambda(j)(T_j u {eps t_i}) = +- NA_j(-eps t_i),  plus the avoidance
 atom s_Lambda(T_j) = +- NA_j(0).  For each atom report:
   - integer content, sign-uniformity, size;
   - the NESTED LEX-EXTREME integer coefficients over ALL variable orders
     (the certificate candidates): for each order, take repeatedly the leading
     coefficient w.r.t. the next variable; result is an integer.  We list the
     DISTINCT extreme integers with a sample order each.
 Goal: for every atom find orders whose extreme integer is +-2^a, and map
 where the 3s appear (slice/Weyl-count prediction).

   magma -b G:=3 p34atoms.m
*****************************************************************************/
if not assigned G then G := "3"; end if;
g := StringToInteger(G);

P := PolynomialRing(Integers(), g);
AssignNames(~P, ["t" cat IntegerToString(i) : i in [1..g]]);
ts := [P.i : i in [1..g]];
PS := PolynomialRing(P); z := PS.1;

function NestedExtreme(p, ord)      // ord = sequence of variable indices
  for v in ord do
    if p eq 0 then return 0; end if;
    p := Coefficient(p, v, Degree(p, v));
  end for;
  error if p eq 0 or TotalDegree(p) gt 0, "nested extreme not integer";
  return Integers()!p;
end function;

function FacInt(n)
  if n eq 0 then return "0"; end if;
  s := n lt 0 select "-" else "";
  n := AbsoluteValue(n);
  if n eq 1 then return s cat "1"; end if;
  return s cat &cat[Sprintf("%o^%o.", q[1], q[2]) : q in Factorization(n)];
end function;

orders := [o : o in Permutations({1..g})];

procedure ReportAtom(tag, p, orders)
  error if p eq 0, tag cat " IS ZERO";
  cs := Coefficients(p);
  su := &and[c gt 0 : c in cs] or &and[c lt 0 : c in cs];
  printf "%-22o cont=%-4o %o t, deg %o, sign-uniform %o\n",
    tag, Integers()!Content(p), #Terms(p), TotalDegree(p), su;
  seen := AssociativeArray(); good := [];
  for o in orders do
    e := NestedExtreme(p, o);
    if not IsDefined(seen, e) then seen[e] := o; end if;
    ae := AbsoluteValue(e);
    if ae eq 2^Valuation(ae, 2) then Append(~good, o); end if;
  end for;
  printf "    extreme ints: ";
  for e in Keys(seen) do printf "%o (ord %o)  ", FacInt(e), seen[e]; end for;
  printf "\n    2-power orders: %o of %o\n", #good, #orders;
end procedure;

for j in [1..g] do
  T := ts cat ts[1..j]; Gj := g + j;
  Ez := &*[PS| 1 + t*z : t in T];
  ee := func<r | (r lt 0 or r gt Gj) select P!0 else Coefficient(Ez, r)>;
  M := Matrix(P, g, g, [[ee(Gj - (2*i - 1) + m) : m in [0..g-1]] : i in [1..g]]);
  rhs := [-ee(Gj - (2*i - 1) + g) : i in [1..g]];
  NAc := [P|];
  for m in [0..g-1] do
    Mm := M; for r in [1..g] do Mm[r][m+1] := rhs[r]; end for;
    Append(~NAc, Determinant(Mm));
  end for;
  Append(~NAc, Determinant(M));
  printf "== j=%o ==\n", j;
  ReportAtom(Sprintf("s_L(T_%o) [avoid]", j), NAc[1], orders);
  ReportAtom(Sprintf("detM_%o", j), NAc[g+1], orders);
  evs := j lt g select [j, j+1] else [j];             // mirror at t_j; step at t_{j+1}
  for i in evs do
    ap := &+[P| NAc[m+1]*ts[i]^m : m in [0..g]];       // NA_j(+t_i) ~ s(T u {-t_i})
    am := &+[P| NAc[m+1]*(-ts[i])^m : m in [0..g]];    // NA_j(-t_i) ~ s(T u {+t_i})
    ReportAtom(Sprintf("s(T_%o u {+t%o})", j, i), am, orders);
    ReportAtom(Sprintf("s(T_%o u {-t%o})", j, i), ap, orders);
  end for;
end for;
quit;
