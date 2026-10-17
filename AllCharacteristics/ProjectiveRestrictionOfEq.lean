import AllCharacteristics.HypersurfaceFiberNaturality

/-!
# Fiber restriction with a specified composite coefficient map

A proved equality with a composite coefficient map supplies an actual
Cartesian restriction morphism, avoiding changes of the chosen source fiber.
Canonical hypersurface comparisons remain natural for these restrictions.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Restriction of the fiber over a specified map equal to the composite coefficient map. -/
noncomputable def projectiveFiberRestrictionOfEq (f : R →+* A) (g : A →+* B) (k : R →+* B)
    (I : HomogeneousIdeal (homogeneousSubmodule σ R)) (h : g.comp f = k) :
    pullback (toBase I) (Spec.map (CommRingCat.ofHom k)) ⟶
      pullback (toBase I) (Spec.map (CommRingCat.ofHom f)) :=
  pullbackRestriction (toBase I) (Spec.map (CommRingCat.ofHom f))
    (Spec.map (CommRingCat.ofHom k)) (Spec.map (CommRingCat.ofHom g))
    ((Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm.trans
      (congrArg (fun a : R →+* B ↦ Spec.map (CommRingCat.ofHom a)) h))

/-- The specified restriction preserves the original projective-space projection. -/
theorem projectiveFiberRestrictionOfEq_fst (f : R →+* A) (g : A →+* B) (k : R →+* B)
    (I : HomogeneousIdeal (homogeneousSubmodule σ R)) (h : g.comp f = k) :
    projectiveFiberRestrictionOfEq f g k I h ≫ pullback.fst (toBase I) (Spec.map (CommRingCat.ofHom f)) =
      pullback.fst (toBase I) (Spec.map (CommRingCat.ofHom k)) :=
  pullbackRestriction_fst _ _ _ _ _

/-- Its coefficient-base projection is the specified spectrum map. -/
theorem projectiveFiberRestrictionOfEq_snd (f : R →+* A) (g : A →+* B) (k : R →+* B)
    (I : HomogeneousIdeal (homogeneousSubmodule σ R)) (h : g.comp f = k) :
    projectiveFiberRestrictionOfEq f g k I h ≫ pullback.snd (toBase I) (Spec.map (CommRingCat.ofHom f)) =
      pullback.snd (toBase I) (Spec.map (CommRingCat.ofHom k)) ≫ Spec.map (CommRingCat.ofHom g) :=
  pullbackRestriction_snd _ _ _ _ _

/-- The specified restriction is an actual Cartesian base change. -/
theorem isPullback_projectiveFiberRestrictionOfEq (f : R →+* A) (g : A →+* B) (k : R →+* B)
    (I : HomogeneousIdeal (homogeneousSubmodule σ R)) (h : g.comp f = k) :
    IsPullback (projectiveFiberRestrictionOfEq f g k I h)
      (pullback.snd (toBase I) (Spec.map (CommRingCat.ofHom k)))
      (pullback.snd (toBase I) (Spec.map (CommRingCat.ofHom f))) (Spec.map (CommRingCat.ofHom g)) :=
  isPullback_pullbackRestriction _ _ _ _ _

/-- Canonical hypersurface comparisons are natural when both composite
coefficient maps are specified by equal homomorphisms. -/
theorem hypersurfaceFiberComparison_naturality_of_eq (b : R →+* A)
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d)
    (c : S →+* A) (q : MvPolynomial σ S) (hq : q.IsHomogeneous d)
    (h : equationIdeal (p.map b) (hp.map b) = equationIdeal (q.map c) (hq.map c))
    (g : A →+* B) (b' : R →+* B) (c' : S →+* B) (hb : g.comp b = b') (hc : g.comp c = c')
    (h' : equationIdeal (p.map b') (hp.map b') = equationIdeal (q.map c') (hq.map c')) :
    (hypersurfaceFiberComparison b' p hp c' q hq h').hom ≫
      projectiveFiberRestrictionOfEq c g c' (equationIdeal q hq) hc =
    projectiveFiberRestrictionOfEq b g b' (equationIdeal p hp) hb ≫
      (hypersurfaceFiberComparison b p hp c q hq h).hom := by
  subst b'
  subst c'
  exact hypersurfaceFiberComparison_naturality b p hp c q hq h g

end HomogeneousProjective
end AllCharacteristics
