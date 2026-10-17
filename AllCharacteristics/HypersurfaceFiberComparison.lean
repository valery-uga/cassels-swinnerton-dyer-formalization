import AllCharacteristics.HypersurfaceCoefficientNaturality
import AllCharacteristics.IsomorphismComparison

/-!
# Coherent comparison of actual hypersurface fibers

Equal specialized homogeneous ideals identify the actual pullback fibers.
These identifications preserve the base and satisfy identity and composition.
For unit multiples, the comparison is the previously constructed reduction
and scaling isomorphism, so these coherence laws apply to that construction.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R S T A : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing A]
variable {σ : Type} {d : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Equations differing by a specified unit generate the same homogeneous ideal. -/
theorem equationIdeal_eq_of_unit_multiple (p q : MvPolynomial σ A)
    (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous d) (a : A) (ha : IsUnit a)
    (h : p = C a * q) : equationIdeal p hp = equationIdeal q hq :=
  (equationIdeal_congr p (C a * q) hp (hq.C_mul a) h).trans
    (equationIdeal_C_mul_of_isUnit a ha q hq)

/-- Exact equation reduction is base change preceded by the canonical
identification of the equal specialized equations. -/
theorem hypersurfaceReductionIso_eq_baseChangeIso (b : R →+* A)
    (p : MvPolynomial σ R) (hp : p.IsHomogeneous d)
    (q : MvPolynomial σ A) (hq : q.IsHomogeneous d) (h : p.map b = q) :
    hypersurfaceReductionIso b p hp q hq h =
      eqToIso (congrArg scheme (equationIdeal_congr q (p.map b) hq (hp.map b) h.symm)) ≪≫
        hypersurfaceBaseChangeIso b p hp := by
  subst q
  exact (Iso.refl_trans (hypersurfaceBaseChangeIso b p hp)).symm

/-- Equal specialized ideals give a canonical isomorphism of actual pullback fibers. -/
noncomputable def hypersurfaceFiberComparison (b : R →+* A)
    (p : MvPolynomial σ R) (hp : p.IsHomogeneous d)
    (c : S →+* A) (q : MvPolynomial σ S) (hq : q.IsHomogeneous d)
    (h : equationIdeal (p.map b) (hp.map b) = equationIdeal (q.map c) (hq.map c)) :
    pullback (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b)) ≅
      pullback (hypersurfaceToBase q hq) (Spec.map (CommRingCat.ofHom c)) :=
  isomorphismComparison (hypersurfaceBaseChangeIso b p hp)
    (hypersurfaceBaseChangeIso c q hq) (congrArg scheme h)

/-- The canonical fiber comparison preserves the common coefficient spectrum. -/
theorem hypersurfaceFiberComparison_hom_snd (b : R →+* A)
    (p : MvPolynomial σ R) (hp : p.IsHomogeneous d)
    (c : S →+* A) (q : MvPolynomial σ S) (hq : q.IsHomogeneous d)
    (h : equationIdeal (p.map b) (hp.map b) = equationIdeal (q.map c) (hq.map c)) :
    (hypersurfaceFiberComparison b p hp c q hq h).hom ≫
      pullback.snd (hypersurfaceToBase q hq) (Spec.map (CommRingCat.ofHom c)) =
    pullback.snd (hypersurfaceToBase p hp) (Spec.map (CommRingCat.ofHom b)) :=
  isomorphismComparison_hom_toBase (hypersurfaceBaseChangeIso b p hp)
    (hypersurfaceBaseChangeIso c q hq) (congrArg scheme h) _ _ _ _
    (hypersurfaceBaseChangeIso_hom_snd b p hp) (hypersurfaceBaseChangeIso_hom_snd c q hq)
    (eqToHom_scheme_toBase _ _ h)

/-- Comparing a fiber with itself gives its identity isomorphism. -/
theorem hypersurfaceFiberComparison_self (b : R →+* A)
    (p : MvPolynomial σ R) (hp : p.IsHomogeneous d) :
    hypersurfaceFiberComparison b p hp b p hp rfl = Iso.refl _ :=
  isomorphismComparison_self (hypersurfaceBaseChangeIso b p hp)

/-- Canonical comparisons compose without any additional choice of fiber identifications. -/
theorem hypersurfaceFiberComparison_comp (b : R →+* A)
    (p : MvPolynomial σ R) (hp : p.IsHomogeneous d)
    (c : S →+* A) (q : MvPolynomial σ S) (hq : q.IsHomogeneous d)
    (e : T →+* A) (r : MvPolynomial σ T) (hr : r.IsHomogeneous d)
    (h : equationIdeal (p.map b) (hp.map b) = equationIdeal (q.map c) (hq.map c))
    (h' : equationIdeal (q.map c) (hq.map c) = equationIdeal (r.map e) (hr.map e)) :
    hypersurfaceFiberComparison b p hp c q hq h ≪≫
      hypersurfaceFiberComparison c q hq e r hr h' =
    hypersurfaceFiberComparison b p hp e r hr (h.trans h') :=
  isomorphismComparison_comp (hypersurfaceBaseChangeIso b p hp)
    (hypersurfaceBaseChangeIso c q hq) (hypersurfaceBaseChangeIso e r hr)
    (congrArg scheme h) (congrArg scheme h')

/-- For equations related by a unit, the canonical fiber comparison is exactly
reduction followed by scaling and base change. -/
theorem hypersurfaceFiberComparison_eq_reduction_scaling (b : R →+* A)
    (p : MvPolynomial σ R) (hp : p.IsHomogeneous d)
    (c : S →+* A) (q : MvPolynomial σ S) (hq : q.IsHomogeneous d)
    (a : A) (ha : IsUnit a) (h : p.map b = C a * q.map c) :
    hypersurfaceFiberComparison b p hp c q hq
      (equationIdeal_eq_of_unit_multiple (p.map b) (q.map c) (hp.map b) (hq.map c) a ha h) =
    (hypersurfaceReductionIso b p hp (C a * q.map c) ((hq.map c).C_mul a) h).symm ≪≫
      (hypersurfaceScalingIso a ha (q.map c) (hq.map c) ≪≫ hypersurfaceBaseChangeIso c q hq) := by
  rw [hypersurfaceReductionIso_eq_baseChangeIso]
  exact isomorphismComparison_factor (hypersurfaceBaseChangeIso b p hp)
    (hypersurfaceBaseChangeIso c q hq)
    (congrArg scheme (equationIdeal_congr (p.map b) (C a * q.map c)
      (hp.map b) ((hq.map c).C_mul a) h))
    (congrArg scheme (equationIdeal_C_mul_of_isUnit a ha (q.map c) (hq.map c)))

end HomogeneousProjective
end AllCharacteristics
