// Check: on the cusp y^2 = X^N (N = 2g+1), the point-by-point fold tau + tau - tau
// with phase 2 in REVERSED order (add iota P_g, ..., iota P_1) satisfies
//   D_{g+m} = D_{g-m}  (same chain, walked backwards),
// and in particular returns to the base at stage 2g.
// Also record the step-condition values (disjointness U_j(x_P)).

Q := Rationals();
P<X> := PolynomialRing(Q);

function CRTinterp(V, U, x0, y0)
  // V_c = V + h*U with V_c(x0) = y0  (disjoint composition, deg 1 point)
  h := (y0 - Evaluate(V, x0))/Evaluate(U, x0);
  return V + h*U;
end function;

function ReduceStep(f, Uc, Vc)
  U2 := (f - Vc^2) div Uc;
  U2 := U2 / LeadingCoefficient(U2);
  V2 := (-Vc) mod U2;
  return U2, V2;
end function;

procedure runfold(g, ts, reversed)
  N := 2*g+1;
  f := X^N;
  xs := [t^2 : t in ts];
  ys := [t^N : t in ts];
  // base: interpolating Mumford datum
  U0 := &*[X - x : x in xs];
  V0 := Interpolation(xs, ys);
  states := [<U0, V0>];
  U := U0; V := V0;
  conds := [];
  // phase 1: step 1 doubles P_1 (P_1 in support): composed sqrt needs tangency
  //   V_c = V + h*U with (f - V_c^2) divisible by (X-x1)^2.
  x1 := xs[1]; y1 := ys[1];
  // condition value for doubling: 2*y1*U'(x1) (denominator of h)
  dU := Derivative(U);
  cond0 := 2*y1*Evaluate(dU, x1);
  Append(~conds, cond0);
  // solve: d/dX (f - (V+h*U)^2) at x1 = 0 ; note V(x1)=y1, U(x1)=0
  df := Derivative(f); dV := Derivative(V);
  h := (Evaluate(df, x1) - 2*y1*Evaluate(dV, x1)) / (2*y1*Evaluate(dU, x1));
  Vc := V + h*U; Uc := U*(X - x1);
  U, V := ReduceStep(f, Uc, Vc);
  Append(~states, <U,V>);
  for j in [2..g] do
    x0 := xs[j]; y0 := ys[j];
    Append(~conds, Evaluate(U, x0));
    Vc := CRTinterp(V, U, x0, y0); Uc := U*(X - x0);
    U, V := ReduceStep(f, Uc, Vc);
    Append(~states, <U,V>);
  end for;
  // phase 2
  order2 := reversed select [g..1 by -1] else [1..g];
  for m in order2 do
    x0 := xs[m]; y0 := -ys[m];
    Append(~conds, Evaluate(U, x0));
    Vc := CRTinterp(V, U, x0, y0); Uc := U*(X - x0);
    U, V := ReduceStep(f, Uc, Vc);
    Append(~states, <U,V>);
  end for;
  printf "g=%o reversed=%o : all conds nonzero: %o\n", g, reversed,
    &and[c ne 0 : c in conds];
  // check retracing: D_{g+m} = D_{g-m}?
  ok := true;
  for m in [1..g] do
    same := states[g+m+1] eq states[g-m+1];
    printf "  D_%o = D_%o : %o\n", g+m, g-m, same;
    ok := ok and same;
  end for;
  printf "  retrace(all): %o ; returns to base: %o\n", ok,
    states[2*g+1] eq states[1];
end procedure;

for g in [2,3,4] do
  ts := [Q | 2, 3, 5, 7, 11][1..g];
  runfold(g, ts, true);
  runfold(g, ts, false);
end for;
quit;
