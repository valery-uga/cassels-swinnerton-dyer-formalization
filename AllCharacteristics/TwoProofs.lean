import PfaffianDescent.VoisinDegreeElevenActualNativeEffectiveEightFactory
import AllCharacteristics.CubicSurfaceMain
import AllCharacteristics.TwistedCubicLemma
import PfaffianDescent.ClosedPointCycles
import PfaffianDescent.CoplanarConicDescent
import PfaffianDescent.IncidenceDegreeTwoOpen
import PfaffianDescent.ProjectivePfaffian
import PfaffianDescent.QuinticGeometricPresentation
import PfaffianDescent.QuarticTwistedCubicSmooth
import PfaffianDescent.ReducedProjectiveFivePoints

/-!
# Paper-facing consequences for `2-proofs.tex`

This module collects the checked theorem statements used in
`../2-proofs.tex`.  Coray's degree `1/4/10` alternative remains external. The public
main, finite-point and smooth-extension statements use the internally proved
actual native degree-ten factory. Conditional adapters retain explicit
effective-degree-four or point-geometry assumptions.  The intrinsic translation from a base-changed embedded curve to a
twisted-cubic coordinate certificate is likewise explicit in the direct
twisted-cubic statements.  Ma's lifting statement is imported as a theorem
from `MaCubicPencilLifting`.

-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
open HomogeneousProjective
open PfaffianDescent
open scoped BigOperators

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The scheme-level homogeneous-presentation form of the paper's
`lem:twisted-cubic`. -/
theorem twoProofs_twisted_cubic
    {k : Type u} [Field k] [PerfectField k]
    (C : ProjectiveCurveWithTwistedCubicPresentation k) :
    C.IsTwistedCubic ∧
      ∃ e : C.curve ≅ projectiveLineProj k,
        e.hom ≫ projectiveLineProjToBase k = C.toBase ∧
          ∃ s : Spec (.of k) ⟶ C.curve, s ≫ C.toBase = 𝟙 _ :=
  C.twisted_cubic

/-- Direct smooth-embedding form of `lem:twisted-cubic` over a perfect field.
The coordinate hypothesis refers to the canonical homogeneous vanishing ideal
of the supplied ambient embedding. -/
theorem twoProofs_twisted_cubic_smooth_embedding
    {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}}
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i]
    (hsmooth : Smooth (i ≫ ambientToBase))
    (hgeo : QuarticNet.GeometricallyStandardTwistedCubic
      (closedImmersionVanishingIdeal i)) :
    QuarticNet.GroundTwistedCubicPresentation (closedImmersionVanishingIdeal i) ∧
      ∃ r : X ≅ scheme (closedImmersionVanishingIdeal i),
        r.hom ≫ quotientProjMap (closedImmersionVanishingIdeal i) = i ∧
          ∃ e : X ≅ projectiveLineProj k,
            e.hom ≫ projectiveLineProjToBase k = i ≫ ambientToBase ∧
              ∃ s : Spec (.of k) ⟶ X, s ≫ i ≫ ambientToBase = 𝟙 _ :=
  smoothProjectiveCurve_twisted_cubic i hsmooth hgeo

/-- The direct algebraic-closure-base-change form of the paper's
`lem:twisted-cubic`.  It takes the standard-cubic presentation after scalar
extension as its geometric input, rather than requiring a separately named
coordinate certificate. -/
theorem twoProofs_twisted_cubic_smooth_embedding_of_algebraicClosure_presentation
    {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}}
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i]
    (hsmooth : Smooth (i ≫ ambientToBase))
    (hbar : IsTwistedCubicAfterCoefficientExtension
      (algebraMap k (AlgebraicClosure k)) i) :
    QuarticNet.GroundTwistedCubicPresentation (closedImmersionVanishingIdeal i) ∧
      ∃ r : X ≅ scheme (closedImmersionVanishingIdeal i),
        r.hom ≫ quotientProjMap (closedImmersionVanishingIdeal i) = i ∧
          ∃ e : X ≅ projectiveLineProj k,
            e.hom ≫ projectiveLineProjToBase k = i ≫ ambientToBase ∧
              ∃ s : Spec (.of k) ⟶ X, s ≫ i ≫ ambientToBase = 𝟙 _ :=
  smoothProjectiveCurve_twisted_cubic_of_algebraicClosure_presentation i hsmooth hbar

/-- Direct arbitrary-field form of `lem:twisted-cubic` when the canonical
ideal has a separable geometric standardization. -/
theorem twoProofs_twisted_cubic_smooth_embedding_separable
    {k : Type u} [Field k]
    {X : Scheme.{u}}
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i]
    (hsmooth : Smooth (i ≫ ambientToBase))
    (hgeo : QuarticNet.SeparableGeometricallyStandardTwistedCubic
      (closedImmersionVanishingIdeal i)) :
    QuarticNet.GroundTwistedCubicPresentation (closedImmersionVanishingIdeal i) ∧
      ∃ r : X ≅ scheme (closedImmersionVanishingIdeal i),
        r.hom ≫ quotientProjMap (closedImmersionVanishingIdeal i) = i ∧
          ∃ e : X ≅ projectiveLineProj k,
            e.hom ≫ projectiveLineProjToBase k = i ≫ ambientToBase ∧
              ∃ s : Spec (.of k) ⟶ X, s ≫ i ≫ ambientToBase = 𝟙 _ :=
  smoothProjectiveCurve_twisted_cubic_separable i hsmooth hgeo

/-- The perfect-field homogeneous-ideal form of the paper's
`lem:twisted-cubic`.  It concludes both the standard cubic presentation in
`P³` and an isomorphism with `P¹` over the base field. -/
theorem twoProofs_twisted_cubic_descent_perfect
    {k : Type u} [Field k] [PerfectField k]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    (hgeo : QuarticNet.GeometricallyStandardTwistedCubic I) :
    QuarticNet.GroundTwistedCubicPresentation I ∧
      ∃ e : scheme I ≅ projectiveLineProj k,
        e.hom ≫ projectiveLineProjToBase k = toBase I ∧
          Smooth (toBase I) ∧
            ∃ s : Spec (.of k) ⟶ scheme I, s ≫ toBase I = 𝟙 _ := by
  exact EmbeddedGeometricallyStandardTwistedCubic.descent_perfect ⟨I, hgeo⟩

/-- The arbitrary-field homogeneous-ideal form when the geometric
standardization is defined over the separable closure. -/
theorem twoProofs_twisted_cubic_descent_separable
    {k : Type u} [Field k]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    (hgeo : QuarticNet.SeparableGeometricallyStandardTwistedCubic I) :
    QuarticNet.GroundTwistedCubicPresentation I ∧
      ∃ e : scheme I ≅ projectiveLineProj k,
        e.hom ≫ projectiveLineProjToBase k = toBase I ∧
          Smooth (toBase I) ∧
            ∃ s : Spec (.of k) ⟶ scheme I, s ≫ toBase I = 𝟙 _ := by
  let hground : QuarticNet.GroundTwistedCubicPresentation I :=
    QuarticNet.groundTwistedCubicPresentation_of_separableGeometricallyStandardTwistedCubic hgeo
  obtain ⟨e, he, hsmooth, s, hs⟩ :=
    QuarticNet.twistedCubic_descent_separable_overBase hgeo
  exact ⟨hground, e, he, hsmooth, s, hs⟩

/-- The characteristic-not-two form of `lem:incidence`: the common-isotropic
incidence scheme is finite étale of degree two over a nonempty open set of
triples of alternating forms.  The explicit good triple is retained in the
underlying proof to establish nonemptiness. -/
theorem twoProofs_incidence_finite_etale_degree_two_open
    {k : Type u} [Field k] [NeZero (2 : k)] :
    ∃ U : (alternatingTripleScheme k).Opens,
      (U : Set (alternatingTripleScheme k)).Nonempty ∧
      IsFinite (incidenceToTriples k ∣_ U) ∧ Etale (incidenceToTriples k ∣_ U) ∧
      ∀ x : U.toScheme, (incidenceToTriples k ∣_ U).finrank x = 2 := by
  obtain ⟨U, hnonempty, -, hfinite, hetale, hdegree⟩ :=
    incidence_finite_etale_degree_two_open k
  exact ⟨U, hnonempty, hfinite, hetale, hdegree⟩

/-- Cassels's degree-four/degree-five alternative in `2-proofs.tex`.  The
checked statement is stronger than the paper's characteristic-zero form: it
holds for every field. -/
theorem twoProofs_cassels_four_five
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    (∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4) ↔
    (∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 5) :=
  cubic_effective_degree_four_iff_five p hp hne

/-- The secant lemma from `2-proofs.tex`: an effective zero-cycle of degree
one or two on a cubic hypersurface supplies a rational point.  The checked
form works over every field and does not require smoothness. -/
theorem twoProofs_secant
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 1 ∨
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 2) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  hypersurface_section_of_effective_cycle_degree_one_or_two p hp z hz

/-- The coplanar case in the first part of `lem:position`: a degree-four or
degree-five closed point of a smooth cubic surface lying in a ground-field
plane yields a rational section.  For degree five this is the plane conic and
residual-intersection argument; degree four is already covered by the direct
degree-four descent theorem. -/
theorem twoProofs_coplanar_degree_four_or_five_has_point
    {k : Type u} [Field k] [CharZero k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 4 ∨
      (hypersurfaceToBase p hp).residueDegree x.1 = 5)
    (c : Fin 4 → k) (hc : c ≠ 0)
    (hplane : Ideal.Quotient.mk (equationIdeal p hp).toIdeal
      (homogeneousLinearForm c) ∈ x.1.asHomogeneousIdeal.toIdeal) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  rcases hx with hfour | hfive
  · exact cubic_section_of_closedPoint_degree_four_or_five p hp hne x (Or.inl hfour)
  · exact PfaffianDescent.cubic_coplanar_degree_five_conic_descent
      p hp x hfive c hc hplane

/-- The noncoplanar part of `lem:position` for degree-five coordinates.  If
the point is not contained in a ground-field plane, its five conjugates in
the finite Galois splitting field are in general linear position. -/
theorem twoProofs_quintic_non_coplanar_general_position
    {k L : Type u} [Field k] [CharZero k] [Field L] [Algebra k L]
    [FiniteDimensional k L]
    (hdim : Module.finrank k L = 5) (x : Fin 4 → L)
    (hnonplanar : ¬ ∃ c : Fin 4 → k, c ≠ 0 ∧ ∑ j, c j • x j = 0) :
    PfaffianDescent.FivePointGeneralPosition
      (fun i j => PfaffianDescent.quinticSplittingEmbeddings hdim i (x j)) := by
  rcases PfaffianDescent.quintic_coordinate_position_dichotomy hdim x with
    hplane | hposition
  · exact (hnonplanar hplane).elim
  · exact hposition

/-- The degree-four coordinate form of the noncoplanar part of
`lem:position`.  Four homogeneous coordinates with no ground-field plane
relation are linearly independent, so a degree-four point is in the required
linear general position. -/
theorem twoProofs_quartic_non_coplanar_linear_independent
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    (x : Fin 4 → L)
    (hnonplanar : ¬ ∃ c : Fin 4 → k, c ≠ 0 ∧ ∑ j, c j • x j = 0) :
    LinearIndependent k x := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hzero : c = 0 := by
    by_contra hne
    exact hnonplanar ⟨c, hne, hc⟩
  simp [hzero]

/-- The paper's Pfaffian theorem: over a field where two is nonzero, a linear
six-by-six alternating Pfaffian presentation produces a rational section of
the presented cubic hypersurface. -/
theorem twoProofs_pfaffian_cubic_has_point
    {k : Type u} [Field k] [NeZero (2 : k)]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (A : Fin 4 → Mat k 6) (hA : ∀ i, IsAlternating (A i))
    (hpresentation : (pfaffianCubic A).toMvPolynomial = p) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  projective_pfaffian_to_point p hp A hA hpresentation

/-- The actual projective-scheme form of `lem:presentation`: every cubic
containing a reduced length-five closed subscheme in geometric general
position has a linear six-by-six alternating Pfaffian presentation. -/
theorem twoProofs_reduced_length_five_subscheme_pfaffian
    {k : Type u} [Field k] [CharZero k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} [IsReduced Z]
    (i : Z ⟶ hypersurface p hp) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase p hp)]
    (hlen : finiteSchemeRank (i ≫ hypersurfaceToBase p hp) = 5)
    (hposition : ProjectiveGeometricGeneralPosition (equationIdeal p hp) i) :
    ∃ A : Fin 4 → Mat k 6, (∀ j, IsAlternating (A j)) ∧
      (pfaffianCubic A).toMvPolynomial = p :=
  reduced_length_five_subscheme_pfaffian p hp i hlen hposition

/-- The noncoplanar branch of the degree-five proof.  Four linearly
independent coordinates of a degree-five point give the Pfaffian
presentation, and the Pfaffian argument then gives a rational section. -/
theorem twoProofs_non_coplanar_quintic_has_point
    {k L : Type u} [Field k] [CharZero k] [Field L] [Algebra k L]
    [FiniteDimensional k L]
    (hdim : Module.finrank k L = 5)
    (x : Fin 4 → L) (hx : LinearIndependent k x)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (heval : MvPolynomial.eval₂ (algebraMap k L) x p = 0) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  obtain ⟨A, hA, hpresentation⟩ :=
    PfaffianDescent.quintic_geometric_pfaffian_presentation hdim x hx p hp heval
  exact projective_pfaffian_to_point p hp A hA hpresentation

/-- The non-coplanar degree-five branch of `lem:position` followed through
the Pfaffian construction.  The absence of a ground-field plane relation
makes the four coordinates linearly independent, so the geometric Pfaffian
presentation gives a rational point on the cubic. -/
theorem twoProofs_non_coplanar_quintic_has_point_of_not_ground_plane
    {k L : Type u} [Field k] [CharZero k] [Field L] [Algebra k L]
    [FiniteDimensional k L]
    (hdim : Module.finrank k L = 5)
    (x : Fin 4 → L)
    (hnonplanar : ¬ ∃ c : Fin 4 → k, c ≠ 0 ∧ ∑ j, c j • x j = 0)
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (heval : MvPolynomial.eval₂ (algebraMap k L) x p = 0) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ := by
  apply twoProofs_non_coplanar_quintic_has_point hdim x
  · rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hzero : c = 0 := by
      by_contra hne
      exact hnonplanar ⟨c, hne, hc⟩
    simp [hzero]
  · exact heval

/-- The degree-five theorem in `2-proofs.tex`, in its scheme-theoretic form.
The underlying arithmetic proof does not need smoothness. -/
theorem twoProofs_degree_five_has_point
    {k : Type u} [Field k] [CharZero k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : EffectiveZeroCycle (hypersurface p hp))
    (hz : EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 5) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  projective_cubic_effective_cycle_degree_five_to_point p hp z hz

/-- The direct degree-four conclusion of `2-proofs.tex`.  The checked proof
is stronger: it works over every field, so in particular over perfect ones. -/
theorem twoProofs_degree_four_closed_point_has_point
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 4) :
    ∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _ :=
  cubic_section_of_closedPoint_degree_four_or_five p hp hne x (Or.inl hx)

/-- Ma's degree-preserving smooth-point lifting statement used in the
specialization section of the paper is internally proved for every field. -/
theorem twoProofs_ma_cubic_pencil_lifting
    (k : Type u) [Field k] :
    MaCubicPencilPointLiftingFor k :=
  maCubicPencilPointLiftingFor k

/-- `lem:singular-point` in homogeneous coordinates.  A point over a finite
extension of degree prime to three either descends or is replaced by a smooth
point over that same extension.  The proof includes the double- and
triple-point cases in all characteristics. -/
theorem twoProofs_singular_point_or_smooth_extension_point
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hdegree : Nat.Coprime (Module.finrank k L) 3)
    (x : Fin 4 → L) (hx : x ≠ 0)
    (heval : p.eval₂ (algebraMap k L) x = 0) :
    (∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0) ∨
      ∃ q : Fin 4 → L,
        IsSmoothCubicCoordinatePoint (p.map (algebraMap k L)) q :=
  cubic_point_or_smooth_extension_point p hp hdegree x hx heval

/-- The substantive descent step of `prop:smoothing`.  A smooth point over a
finite extension is carried through the power-series cubic pencil, Ma's
degree-preserving lift, the characteristic-zero theorem, and proper
specialization to a rational point on the original cubic. -/
theorem twoProofs_smooth_extension_point_descent_of_effectiveDegreeFour
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (geometry : ∀ (K : Type u) [Field K] [CharZero K],
      VoisinDegreeTenEffectiveDegreeFourFor K)
    {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    (ma : MaCubicPencilPointLiftingFor k)
    (p q : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hq0 : q ≠ 0)
    (hqsmooth : Smooth (hypersurfaceToBase q hq))
    (x : Fin 4 → L)
    (hxsmooth : IsSmoothCubicCoordinatePoint (p.map (algebraMap k L)) x)
    (hdegree : Nat.Coprime (Module.finrank k L) 3) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 :=
  cubic_coordinates_of_smooth_extension_point_of_voisin_ma
    (fun K _ _ => voisinDegreeOneOrFourFor_of_coray_and_effectiveDegreeFour
      (coray K) (geometry K)) ma p q hp hq hq0 hqsmooth x hxsmooth hdegree

/-- A closed point of degree prime to three supplies a degree-one zero-cycle
on a cubic surface.  This is the ``only if'' equivalence in the paper before
the rational-point conclusion is invoked. -/
theorem twoProofs_zeroCycle_degree_one_of_closedPoint_coprime
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (x : closedPoints (hypersurface p hp))
    (hx : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree x.1) 3) :
    ∃ z : ZeroCycle (hypersurface p hp),
      ZeroCycle.degree (hypersurfaceToBase p hp) z = 1 := by
  let z : EffectiveZeroCycle (hypersurface p hp) := Finsupp.single x 1
  have hz : Nat.Coprime (EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z) 3 := by
    simpa [z, EffectiveZeroCycle.degree] using hx
  exact cubicSurface_zeroCycle_degree_one_of_effective_coprime p hp z hz

/-- A degree-one zero-cycle contains a closed point of degree prime to three. -/
theorem twoProofs_exists_closedPoint_coprime_of_zeroCycle_degree_one
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (z : ZeroCycle (hypersurface p hp))
    (hz : ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :
    ∃ x : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree x.1) 3 := by
  obtain ⟨x, _, hx⟩ := ZeroCycle.exists_coprime_degree
    (hypersurfaceToBase p hp) z hz
  exact ⟨x, hx⟩

/-- The two finite-cycle formulations in the main theorem are equivalent,
without using Coray or Voisin. -/
theorem twoProofs_closedPoint_coprime_iff_zeroCycle_degree_one
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) :
    (∃ x : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree x.1) 3) ↔
    (∃ z : ZeroCycle (hypersurface p hp),
      ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) := by
  constructor
  · rintro ⟨x, hx⟩
    exact twoProofs_zeroCycle_degree_one_of_closedPoint_coprime p hp x hx
  · rintro ⟨z, hz⟩
    exact twoProofs_exists_closedPoint_coprime_of_zeroCycle_degree_one p hp z hz

/-- A rational section gives a degree-one zero-cycle. -/
theorem twoProofs_zeroCycle_degree_one_of_section
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (s : Spec (.of k) ⟶ hypersurface p hp)
    (hs : s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    ∃ z : ZeroCycle (hypersurface p hp),
      ZeroCycle.degree (hypersurfaceToBase p hp) z = 1 := by
  obtain ⟨z, hz⟩ := effective_cycle_of_section (hypersurfaceToBase p hp) s hs 1
  refine ⟨z.toZeroCycle, ?_⟩
  rw [EffectiveZeroCycle.degree_toZeroCycle, hz]
  norm_num

/-- The main theorem of `2-proofs.tex` from the minimal degree-ten Voisin
input: an effective degree-four cycle. It applies to arbitrary cubic
hypersurfaces, including singular and nonreduced ones. -/
theorem twoProofs_main_theorem_of_effectiveDegreeFour
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (geometry : ∀ (K : Type u) [Field K] [CharZero K],
      VoisinDegreeTenEffectiveDegreeFourFor K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) :
    (∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) ↔
    (∃ z : ZeroCycle (hypersurface p hp),
      ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) := by
  constructor
  · rintro ⟨s, hs⟩
    exact twoProofs_zeroCycle_degree_one_of_section p hp s hs
  · rintro ⟨z, hz⟩
    exact cubic_section_of_zeroCycle_degree_one_of_voisin
      (fun K _ _ => voisinDegreeOneOrFourFor_of_coray_and_effectiveDegreeFour
        (coray K) (geometry K)) p hp z hz

/-- The main theorem of `2-proofs.tex`, modulo Coray alone. -/
theorem twoProofs_main_theorem
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) :
    (∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) ↔
    (∃ z : ZeroCycle (hypersurface p hp),
      ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :=
  twoProofs_main_theorem_of_effectiveDegreeFour coray
    (fun K _ _ => PfaffianDescent.voisinDegreeTenSelectedAvoidance_actualNative_effectiveDegreeFourFactory (K := K)) p hp


/-- The stronger point-specific Voisin construction implies the minimal
effective-cycle form of the main theorem. -/
theorem twoProofs_main_theorem_of_pointGeometry
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (geometry : ∀ (K : Type u) [Field K] [CharZero K], VoisinDegreeTenPointGeometryFor K)
    {k : Type u} [Field k]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) :
    (∃ s : Spec (.of k) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) ↔
    (∃ z : ZeroCycle (hypersurface p hp),
      ZeroCycle.degree (hypersurfaceToBase p hp) z = 1) :=
  twoProofs_main_theorem_of_effectiveDegreeFour coray
    (fun K _ _ => voisinDegreeTenEffectiveDegreeFourFor_of_pointGeometryFor
      (geometry K)) p hp

/-- The finite-extension formulation in the introduction follows from the
main theorem with the same explicit Coray--Voisin hypotheses. -/
theorem twoProofs_finite_point_coprime_has_point_of_effectiveDegreeFour
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (geometry : ∀ (K : Type u) [Field K] [CharZero K],
      VoisinDegreeTenEffectiveDegreeFourFor K)
    {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hdegree : Nat.Coprime (Module.finrank k L) 3)
    (x : Fin 4 → L) (hx : x ≠ 0)
    (heval : p.eval₂ (algebraMap k L) x = 0) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 :=
  cubic_coordinates_of_finite_point_coprime_of_voisin
    (fun K _ _ => voisinDegreeOneOrFourFor_of_coray_and_effectiveDegreeFour
      (coray K) (geometry K)) p hp hdegree x hx heval

/-- Compatibility adapter from the stronger point-specific construction to
the minimal finite-point theorem. -/
theorem twoProofs_finite_point_coprime_has_point_of_pointGeometry
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    (geometry : ∀ (K : Type u) [Field K] [CharZero K], VoisinDegreeTenPointGeometryFor K)
    {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hdegree : Nat.Coprime (Module.finrank k L) 3)
    (x : Fin 4 → L) (hx : x ≠ 0)
    (heval : p.eval₂ (algebraMap k L) x = 0) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 :=
  twoProofs_finite_point_coprime_has_point_of_effectiveDegreeFour coray
    (fun K _ _ => voisinDegreeTenEffectiveDegreeFourFor_of_pointGeometryFor
      (geometry K)) p hp hdegree x hx heval

/-- Uses the internally proved actual native degree-four factory; only Coray remains external. -/
theorem twoProofs_finite_point_coprime_has_point
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    (hdegree : Nat.Coprime (Module.finrank k L) 3)
    (x : Fin 4 → L) (hx : x ≠ 0)
    (heval : p.eval₂ (algebraMap k L) x = 0) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 :=
  twoProofs_finite_point_coprime_has_point_of_effectiveDegreeFour coray
    (fun K _ _ => PfaffianDescent.voisinDegreeTenSelectedAvoidance_actualNative_effectiveDegreeFourFactory (K := K)) p hp hdegree x hx heval

/-- Uses the internally proved actual native degree-four factory; only Coray remains external. -/
theorem twoProofs_smooth_extension_point_descent
    (coray : ∀ (K : Type u) [Field K] [CharZero K], CorayDegreeOneFourOrTenFor K)
    {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    (p q : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hq0 : q ≠ 0)
    (hqsmooth : Smooth (hypersurfaceToBase q hq))
    (x : Fin 4 → L)
    (hxsmooth : IsSmoothCubicCoordinatePoint (p.map (algebraMap k L)) x)
    (hdegree : Nat.Coprime (Module.finrank k L) 3) :
    ∃ y : Fin 4 → k, y ≠ 0 ∧ p.eval y = 0 :=
  twoProofs_smooth_extension_point_descent_of_effectiveDegreeFour coray
    (fun K _ _ => PfaffianDescent.voisinDegreeTenSelectedAvoidance_actualNative_effectiveDegreeFourFactory (K := K))
    (maCubicPencilPointLiftingFor k) p q hp hq hq0 hqsmooth x hxsmooth hdegree

end AllCharacteristics
