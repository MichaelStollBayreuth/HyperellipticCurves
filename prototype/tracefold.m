// Trace-form additivity along the fold (the invariance identity of
// HyperellipticCurves/Log/Fold/FoldTrace.lean): g in {2, 3} over S = k[x1..xg,y1..yg] truncated at
// total degree < N (model of MvPowerSeries (Fin g + Fin g) O).  Runs the full 2g-step
// fold-F_tau pipeline and then checks, for all 0 <= i < g and 1 <= k <= g:
//   (H) the invariance identity
//         sum_j traceMat(Ufin, sP)(i,j) * dY_k(coeff_j Ufin) = traceMat(UY, sY)(i,k),
//   (A) the aggregation crux (the "trace-form additivity over the moving points"):
//         sum_j A_j^i * dY_k(A_j) * (2 B_j)^-1 = traceMat(UY, sY)(i,k),
//   (S) per-step conservation, mirroring the Lean induction: each phase-1 step increments
//         traceDiff(U, s, i; dY_k) by exactly the point contribution A_j^i*dY_k(A_j)/(2B_j)
//         (traceDiff_cantorCompose + reduce-invariance), each phase-2 step leaves it fixed.
// Conventions match HyperellipticCurves/Curve/TraceDiff.lean:
//   topCoeffMod u p = coeff_{deg u - 1}(p mod u);  traceMat u s i j = -topCoeffMod(T^(i+j)*s);
//   traceDiff d u s i = -topCoeffMod(T^i * dotDer(u) * s).
// Derivatives of degree-<N truncations are correct only mod degree N-1, so all identity
// checks allow a difference supported in total degree >= N-1.

// ---------- truncation helpers ----------
function TruncR(c, N)
  if c eq 0 then return c; end if;
  mons := Monomials(c); cfs := Coefficients(c);
  keep := [ cfs[i]*mons[i] : i in [1..#mons] | TotalDegree(mons[i]) lt N ];
  return IsEmpty(keep) select Parent(c)!0 else &+keep;
end function;

function TruncP(F, N)
  if F eq 0 then return F; end if;
  return Parent(F)![ TruncR(c, N) : c in Coefficients(F) ];
end function;

// residue: all variables -> 0
function ResR(c)
  R := Parent(c);
  return Evaluate(c, [ CoefficientRing(R)!0 : i in [1..Rank(R)] ]);
end function;

function ResP(F, kT)
  if F eq 0 then return kT!0; end if;
  return kT![ ResR(c) : c in Coefficients(F) ];
end function;

// ---------- division by a monic polynomial over the truncated ring ----------
function DivModMonic(a, u, N)
  PT := Parent(u); T := PT.1;
  q := PT!0; r := TruncP(a, N); du := Degree(u);
  while Degree(r) ge du do
    tm := LeadingCoefficient(r) * T^(Degree(r)-du);
    q +:= tm; r := TruncP(r - tm*u, N);
  end while;
  return q, r;
end function;

// ---------- unit inverses (Newton) ----------
function InvUnitR(c, N)          // c in R with ResR(c) ne 0
  i := Parent(c)!(1/ResR(c));
  for it in [1..5] do i := TruncR(i*(2 - c*i), N); end for;
  return i;
end function;

// inverse of W mod monic U (unit mod U at the residue), Newton from a field-level seed w0
function InvModMonic(W, U, w0, N)
  I := Parent(U)!w0;
  for it in [1..5] do
    _, prod := DivModMonic(TruncP(W*I, N), U, N);
    _, I := DivModMonic(TruncP(I*(2 - prod), N), U, N);
  end for;
  return I;
end function;

// Hensel square root V of f mod U with centre vseed (Newton)
function ChartV(U, vseed, fT, N, kT)
  PT := Parent(U); R := CoefficientRing(PT);
  V := PT![ R!c : c in Coefficients(vseed) ];
  w0k := InverseMod(2*vseed, ResP(U, kT));
  for it in [1..6] do
    _, r := DivModMonic(TruncP(V^2 - fT, N), U, N);
    Iv := InvModMonic(TruncP(2*V, N), U, w0k, N);
    _, corr := DivModMonic(TruncP(r*Iv, N), U, N);
    V := TruncP(V - corr, N);
  end for;
  _, chk := DivModMonic(TruncP(V^2 - fT, N), U, N);
  assert chk eq 0;
  return V;
end function;

// Hensel root of U seeded at a0
function HenselRoot(U, a0, N)
  R := CoefficientRing(Parent(U));
  A := R!a0; dU := Derivative(U);
  for it in [1..6] do
    UA := TruncR(Evaluate(U, A), N);
    A := TruncR(A - UA*InvUnitR(TruncR(Evaluate(dU, A), N), N), N);
  end for;
  assert TruncR(Evaluate(U, A), N) eq 0;
  return A;
end function;

// lift a residue Bezout identity rs1*u1 + rs2*u2 + rs3*w3 = 1 by Newton
function LiftTriple(u1, u2, w3, rs1, rs2, rs3, N)
  PT := Parent(u1);
  s1 := PT!rs1; s2 := PT!rs2; s3 := PT!rs3;
  for it in [1..5] do
    E := TruncP(s1*u1 + s2*u2 + s3*w3, N);
    s1 := TruncP(s1*(2 - E), N); s2 := TruncP(s2*(2 - E), N); s3 := TruncP(s3*(2 - E), N);
  end for;
  assert TruncP(s1*u1 + s2*u2 + s3*w3, N) eq 1;
  return s1, s2, s3;
end function;

// ---------- the fold step body ----------
function FoldStep(U, V, xP, yP, s1, s2, s3, fT, N)
  PT := Parent(U); T := PT.1;
  u2 := T - xP; v2 := PT!yP;
  Ucomp := TruncP(U*u2, N);
  cv := TruncP(s1*U*v2 + s2*u2*V + s3*(V*v2 + fT), N);
  _, Vcomp := DivModMonic(cv, Ucomp, N);
  cof, rem := DivModMonic(TruncP(Vcomp^2 - fT, N), Ucomp, N);
  assert rem eq 0;                       // Mumford divisibility of the composed pair
  Unew := TruncP(-cof, N);
  assert Degree(Unew) eq Degree(U) and LeadingCoefficient(Unew) eq 1;
  _, Vnew := DivModMonic(TruncP(-Vcomp, N), Unew, N);
  cof2, rem2 := DivModMonic(TruncP(Vnew^2 - fT, N), Unew, N);
  assert rem2 eq 0;                      // invariant restored
  return Unew, Vnew;
end function;

// ---------- trace-form functionals ----------
function TraceMatEntry(U, s, i, j, N)
  PT := Parent(U); T := PT.1;
  _, r := DivModMonic(TruncP(T^(i+j)*s, N), U, N);
  return -Coefficient(r, Degree(U)-1);
end function;

function TraceDiff(U, s, i, kvar, N)     // d = d/d(variable kvar of R)
  PT := Parent(U); T := PT.1;
  dU := PT![ Derivative(c, kvar) : c in Coefficients(U) ];
  _, r := DivModMonic(TruncP(T^i * dU * s, N), U, N);
  return -Coefficient(r, Degree(U)-1);
end function;

// difference allowed only in the truncation fuzz (total degree >= N-1)
function IsZeroModFuzz(dd, N)
  return dd eq 0 or Min([ TotalDegree(m) : m in Monomials(dd) ]) ge N-1;
end function;

// a Bezout cofactor s with c*U + s*(2V) = 1, lifted from the residue
function StateCofactor(U, V, kT, N)
  g0, al, be := XGCD(ResP(U, kT), 2*ResP(V, kT));
  assert g0 eq 1;
  c, s := LiftTriple(U, TruncP(2*V, N), Parent(U)!0, al, be, kT!0, N);
  return s;
end function;

// ---------- the test ----------
procedure RunTest(g, p, N, avraw, bvraw)
  printf "=== g = %o, p = %o, N = %o ===\n", g, p, N;
  k := GF(p);
  kT<t> := PolynomialRing(k);
  av := [ k!a : a in avraw ]; bv := [ k!b : b in bvraw ];
  R := PolynomialRing(k, 2*g);
  PT<T> := PolynomialRing(R);
  // curve: f = t^(2g+1) + l with f(a_i) = b_i^2; tau = (u, v) the g-point divisor
  fk := t^(2*g+1) + Interpolation(av, [ bv[i]^2 - av[i]^(2*g+1) : i in [1..g] ]);
  uk := &*[ t - av[i] : i in [1..g] ];
  vk := Interpolation(av, bv);
  assert forall{ i : i in [1..g] | Evaluate(fk, av[i]) eq bv[i]^2 };
  assert (vk^2 - fk) mod uk eq 0;
  fT := TruncP(PT![ R!c : c in Coefficients(fk) ], N);
  // the two charts
  UX := PT![ R!c : c in Coefficients(uk) ] + &+[ R.i*T^(i-1) : i in [1..g] ];
  UY := PT![ R!c : c in Coefficients(uk) ] + &+[ R.(g+i)*T^(i-1) : i in [1..g] ];
  VX := ChartV(UX, vk, fT, N, kT);
  VY := ChartV(UY, vk, fT, N, kT);
  // moving points: Hensel roots of the Y-side chart, with V-values
  A := [ HenselRoot(UY, av[i], N) : i in [1..g] ];
  B := [ TruncR(Evaluate(VY, A[i]), N) : i in [1..g] ];
  // the point contribution A_j^i * dY_k(A_j) * (2 B_j)^-1 (traceDiff_single shape)
  contrib := func< j, i, kk |
    TruncR(A[j]^i * Derivative(A[j], g+kk) * InvUnitR(TruncR(2*B[j], N), N), N) >;
  // ---------- run the 2g-step pipeline with per-step conservation check (S) ----------
  U := UX; V := VX;
  td := [ [ TraceDiff(U, StateCofactor(U, V, kT, N), i, g+kk, N)
            : kk in [1..g] ] : i in [0..g-1] ];
  assert forall{ <i, kk> : i in [1..g], kk in [1..g] | td[i][kk] eq 0 };  // X-block Y-constant
  for j in [1..g] do                     // phase 1: the moving points
    if j eq 1 then                       // near-tangent: full residue triple, rs1 = 0
      g0, al, be := XGCD(t - av[1], vk + bv[1]);
      assert g0 eq 1;
      s1, s2, s3 := LiftTriple(UX, T - A[1], TruncP(VX + PT!B[1], N), kT!0, al, be, N);
    else                                 // disjoint: pair Bezout, s3 = 0
      g0, al, be := XGCD(ResP(U, kT), t - av[j]);
      assert g0 eq 1;
      s1, s2, s3 := LiftTriple(U, T - A[j], PT!0, al, be, kT!0, N);
    end if;
    U, V := FoldStep(U, V, A[j], B[j], s1, s2, s3, fT, N);
    sState := StateCofactor(U, V, kT, N);
    for i in [0..g-1], kk in [1..g] do
      tdNew := TraceDiff(U, sState, i, g+kk, N);
      assert IsZeroModFuzz(tdNew - td[i+1][kk] - contrib(j, i, kk), N);
      td[i+1][kk] := tdNew;
    end for;
    printf "phase-1 step %o: conservation ok\n", j;
  end for;
  for m in [1..g] do                     // phase 2: the constant involuted points
    g0, al, be := XGCD(ResP(U, kT), t - av[m]);
    assert g0 eq 1;
    s1, s2, s3 := LiftTriple(U, T - R!av[m], PT!0, al, be, kT!0, N);
    U, V := FoldStep(U, V, R!av[m], R!(-bv[m]), s1, s2, s3, fT, N);
    sState := StateCofactor(U, V, kT, N);
    for i in [0..g-1], kk in [1..g] do
      tdNew := TraceDiff(U, sState, i, g+kk, N);
      assert IsZeroModFuzz(tdNew - td[i+1][kk], N);
      td[i+1][kk] := tdNew;
    end for;
    printf "phase-2 step %o: conservation ok\n", m;
  end for;
  assert ResP(U, kT) eq uk and ResP(V, kT) eq vk;   // centre endpoint = tau
  // ---------- headline (H) and aggregation crux (A) ----------
  sP := StateCofactor(U, V, kT, N);
  sY := StateCofactor(UY, VY, kT, N);
  for i in [0..g-1], kk in [1..g] do
    rhs := TraceMatEntry(UY, sY, i, kk-1, N);
    lhsH := &+[ TruncR(TraceMatEntry(U, sP, i, j, N)
                * Derivative(Coefficient(U, j), g+kk), N) : j in [0..g-1] ];
    assert IsZeroModFuzz(lhsH - rhs, N);
    lhsA := &+[ contrib(j, i, kk) : j in [1..g] ];
    assert IsZeroModFuzz(lhsA - rhs, N);
  end for;
  print "invariance identity ok";
  print "aggregation crux ok";
end procedure;

RunTest(2, 1009, 6, [3, 7], [5, 11]);
RunTest(3, 1009, 5, [3, 7, 10], [5, 11, 13]);
print "ALL CHECKS PASSED";
quit;
