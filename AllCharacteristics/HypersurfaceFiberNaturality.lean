import AllCharacteristics.ProjectiveBaseChangeNaturality
import AllCharacteristics.IsomorphismComparisonNaturality
import AllCharacteristics.HypersurfaceFiberComparison

/-!
# Hypersurface fiber comparisons commute with further base change

The actual comparison of fibers with equal specialized ideals is natural
under every further coefficient homomorphism. The restriction maps on the
pullbacks are the canonical Cartesian maps, not chosen abstract morphisms.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
variable {σ : Type} {d : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Successive specialization gives the ideal of the composite specialized equation. -/
theorem equationIdeal_map_comp (b : R →+* A) (g : A →+* B)
    (p : MvPolynomial σ R) (hp : p.IsHomogeneous d) :
    (equationIdeal (p.map b) (hp.map b)).toIdeal.map (MvPolynomial.map g) =
      (equationIdeal (p.map (g.comp b)) (hp.map (g.comp b))).toIdeal :=
  equationIdeal_map_of_eq g (p.map b) (hp.map b) (p.map (g.comp b)) (hp.map (g.comp b))
    (MvPolynomial.map_map b g p)

/-- Equality of specialized homogeneous ideals persists under further coefficient change. -/
theorem equationIdeal_specialization_eq_map (b : R →+* A)
    (p : MvPolynomial σ R) (hp : p.IsHomogeneous d)
    (c : S →+* A) (q : MvPolynomial σ S) (hq : q.IsHomogeneous d)
    (h : equationIdeal (p.map b) (hp.map b) = equationIdeal (q.map c) (hq.map c))
    (g : A →+* B) :
    equationIdeal (p.map (g.comp b)) (hp.map (g.comp b)) =
      equationIdeal (q.map (g.comp c)) (hq.map (g.comp c)) := by
  apply HomogeneousIdeal.ext
  rw [← equationIdeal_map_comp b g p hp, ← equationIdeal_map_comp c g q hq, h]

/-- The canonical coefficient morphism between successive specialized hypersurfaces. -/
noncomputable def hypersurfaceCoefficientRestriction (b : R →+* A) (g : A →+* B)
    (p : MvPolynomial σ R) (hp : p.IsHomogeneous d) :
    hypersurface (p.map (g.comp b)) (hp.map (g.comp b)) ⟶ hypersurface (p.map b) (hp.map b) :=
  projectiveCoefficientMap g (equationIdeal (p.map b) (hp.map b))
    (equationIdeal (p.map (g.comp b)) (hp.map (g.comp b))) (equationIdeal_map_comp b g p hp)

/-- The coefficient restriction has the given coefficient-spectrum map. -/
theorem hypersurfaceCoefficientRestriction_toBase (b : R →+* A) (g : A →+* B)
    (p : MvPolynomial σ R) (hp : p.IsHomogeneous d) :
    hypersurfaceCoefficientRestriction b g p hp ≫ hypersurfaceToBase (p.map b) (hp.map b) =
      hypersurfaceToBase (p.map (g.comp b)) (hp.map (g.comp b)) ≫ Spec.map (CommRingCat.ofHom g) :=
  projectiveCoefficientMap_toBase _ _ _ _

/-- Hypersurface base-change identification commutes with the actual restriction map. -/
theorem hypersurfaceBaseChangeIso_naturality (b : R →+* A) (g : A →+* B)
    (p : MvPolynomial σ R) (hp : p.IsHomogeneous d) :
    (hypersurfaceBaseChangeIso (g.comp b) p hp).hom ≫
      projectiveFiberRestriction b g (equationIdeal p hp) =
    hypersurfaceCoefficientRestriction b g p hp ≫ (hypersurfaceBaseChangeIso b p hp).hom :=
  projectiveBaseChangeIso_naturality b g (equationIdeal p hp)
    (equationIdeal (p.map b) (hp.map b)) (equationIdeal (p.map (g.comp b)) (hp.map (g.comp b)))
    (equationIdeal_map b p hp) (equationIdeal_map_comp b g p hp)

/-- Canonical isomorphisms of actual hypersurface fibers commute with arbitrary
further coefficient change and the resulting Cartesian restriction maps. -/
theorem hypersurfaceFiberComparison_naturality (b : R →+* A)
    (p : MvPolynomial σ R) (hp : p.IsHomogeneous d)
    (c : S →+* A) (q : MvPolynomial σ S) (hq : q.IsHomogeneous d)
    (h : equationIdeal (p.map b) (hp.map b) = equationIdeal (q.map c) (hq.map c))
    (g : A →+* B) :
    (hypersurfaceFiberComparison (g.comp b) p hp (g.comp c) q hq
      (equationIdeal_specialization_eq_map b p hp c q hq h g)).hom ≫
      projectiveFiberRestriction c g (equationIdeal q hq) =
    projectiveFiberRestriction b g (equationIdeal p hp) ≫
      (hypersurfaceFiberComparison b p hp c q hq h).hom :=
  isomorphismComparison_naturality
    (hypersurfaceBaseChangeIso (g.comp b) p hp) (hypersurfaceBaseChangeIso (g.comp c) q hq)
    (hypersurfaceBaseChangeIso b p hp) (hypersurfaceBaseChangeIso c q hq)
    (congrArg scheme (equationIdeal_specialization_eq_map b p hp c q hq h g)) (congrArg scheme h)
    (hypersurfaceCoefficientRestriction b g p hp) (hypersurfaceCoefficientRestriction c g q hq)
    (projectiveFiberRestriction b g (equationIdeal p hp))
    (projectiveFiberRestriction c g (equationIdeal q hq))
    (hypersurfaceBaseChangeIso_naturality b g p hp) (hypersurfaceBaseChangeIso_naturality c g q hq)
    (projectiveCoefficientMap_transport g
      (equationIdeal (p.map b) (hp.map b)) (equationIdeal (q.map c) (hq.map c))
      (equationIdeal (p.map (g.comp b)) (hp.map (g.comp b)))
      (equationIdeal (q.map (g.comp c)) (hq.map (g.comp c)))
      (equationIdeal_map_comp b g p hp) (equationIdeal_map_comp c g q hq)
      h (equationIdeal_specialization_eq_map b p hp c q hq h g))

end HomogeneousProjective
end AllCharacteristics
