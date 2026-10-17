import AllCharacteristics.AffineSchemeActionOrbits
import AllCharacteristics.InvariantResidueGalois

/-!
# Residue-field orbits for affine scheme actions

The stabilizer of a prime in a finite invariant quotient acts on its residue
field.  The resulting field automorphism carries the canonical residue-field
point to the translate of that point.  This upgrades the orbit statement for
underlying topological points to the embedding-level equivariance needed for
Galois descent of ordered tuples.
-/

open AlgebraicGeometry CategoryTheory
open scoped Pointwise

namespace AllCharacteristics
universe u v

section InvariantSpectrum

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable (G : Type v) [Finite G] [Group G] [MulSemiringAction G A]
variable [SMulCommClass G R A]

/-- The residue-field ring equivalence induced by an element stabilizing a
prime of the ring carrying the action. -/
noncomputable def affineInvariantPrimeResidueStabilizerEquiv
    (q : PrimeSpectrum A) (s : MulAction.stabilizer G q.asIdeal) :
    q.asIdeal.ResidueField ≃+* q.asIdeal.ResidueField := by
  let p : PrimeSpectrum (FixedPoints.subalgebra R A G) :=
    PrimeSpectrum.comap
      (algebraMap (FixedPoints.subalgebra R A G) A) q
  let h : p.asIdeal = q.asIdeal.comap
      (algebraMap (FixedPoints.subalgebra R A G) A) :=
    PrimeSpectrum.comap_asIdeal _ _
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    invariantPrimeResidueAlgebra p.asIdeal q.asIdeal h
  exact (invariantPrimeResidueStabilizerHom
    G p.asIdeal q.asIdeal h s).toRingEquiv

/-- The Galois group of the residue extension above an invariant-quotient
prime, with the quotient prime and its algebra structure kept internal. -/
noncomputable abbrev affineInvariantPrimeResidueGal
    (q : PrimeSpectrum A) :=
  let p : PrimeSpectrum (FixedPoints.subalgebra R A G) :=
    PrimeSpectrum.comap
      (algebraMap (FixedPoints.subalgebra R A G) A) q
  let h : p.asIdeal = q.asIdeal.comap
      (algebraMap (FixedPoints.subalgebra R A G) A) :=
    PrimeSpectrum.comap_asIdeal _ _
  letI := invariantPrimeResidueAlgebra p.asIdeal q.asIdeal h
  Gal(q.asIdeal.ResidueField/p.asIdeal.ResidueField)

/-- Forget the quotient-residue algebra structure on a residue Galois
automorphism, retaining its underlying ring equivalence. -/
noncomputable def affineInvariantPrimeResidueGalRingEquiv
    (q : PrimeSpectrum A) (g : affineInvariantPrimeResidueGal R A G q) :
    q.asIdeal.ResidueField ≃+* q.asIdeal.ResidueField := by
  let p : PrimeSpectrum (FixedPoints.subalgebra R A G) :=
    PrimeSpectrum.comap
      (algebraMap (FixedPoints.subalgebra R A G) A) q
  let h : p.asIdeal = q.asIdeal.comap
      (algebraMap (FixedPoints.subalgebra R A G) A) :=
    PrimeSpectrum.comap_asIdeal _ _
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    invariantPrimeResidueAlgebra p.asIdeal q.asIdeal h
  exact g.toRingEquiv

/-- Every automorphism of the residue Galois extension is realized by an
element stabilizing the prime upstairs. -/
theorem exists_affineInvariantPrimeStabilizer_of_galois
    (q : PrimeSpectrum A)
    (g : affineInvariantPrimeResidueGal R A G q) :
    ∃ s : MulAction.stabilizer G q.asIdeal,
      affineInvariantPrimeResidueStabilizerEquiv R A G q s =
        affineInvariantPrimeResidueGalRingEquiv R A G q g := by
  let p : PrimeSpectrum (FixedPoints.subalgebra R A G) :=
    PrimeSpectrum.comap
      (algebraMap (FixedPoints.subalgebra R A G) A) q
  let h : p.asIdeal = q.asIdeal.comap
      (algebraMap (FixedPoints.subalgebra R A G) A) :=
    PrimeSpectrum.comap_asIdeal _ _
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    invariantPrimeResidueAlgebra p.asIdeal q.asIdeal h
  obtain ⟨s, hs⟩ := invariantPrimeResidueStabilizerHom_surjective
    G p.asIdeal q.asIdeal h g
  refine ⟨s, ?_⟩
  change _ = g.toRingEquiv
  exact congrArg AlgEquiv.toRingEquiv hs

/-- A stabilizer element acts on the canonical residue-field point exactly by
the original action on the affine spectrum. -/
theorem affineInvariantPrimeResidueStabilizer_specMap
    (q : PrimeSpectrum A) (s : MulAction.stabilizer G q.asIdeal) :
    Spec.map (CommRingCat.ofHom
          (affineInvariantPrimeResidueStabilizerEquiv R A G q s).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap A q.asIdeal.ResidueField)) =
      Spec.map (CommRingCat.ofHom
          (algebraMap A q.asIdeal.ResidueField)) ≫
        Spec.map (CommRingCat.ofHom
          (MulSemiringAction.toRingHom G A s.val)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]
  ext x
  let p : PrimeSpectrum (FixedPoints.subalgebra R A G) :=
    PrimeSpectrum.comap
      (algebraMap (FixedPoints.subalgebra R A G) A) q
  let h : p.asIdeal = q.asIdeal.comap
      (algebraMap (FixedPoints.subalgebra R A G) A) :=
    PrimeSpectrum.comap_asIdeal _ _
  letI : Algebra p.asIdeal.ResidueField q.asIdeal.ResidueField :=
    invariantPrimeResidueAlgebra p.asIdeal q.asIdeal h
  change invariantPrimeResidueStabilizerHom G p.asIdeal q.asIdeal h s
      (algebraMap A q.asIdeal.ResidueField x) =
    algebraMap A q.asIdeal.ResidueField (s.val • x)
  exact invariantPrimeResidueStabilizerHom_algebraMap
    G p.asIdeal q.asIdeal h s x

end InvariantSpectrum

section AffineScheme

variable {X S : Scheme.{u}} [IsAffine X]
variable (G : Type v) [Finite G] [Group G]
variable (ρ : G → (X ⟶ X)) (h₁ : ρ 1 = 𝟙 X)
variable (hcomp : ∀ g h : G, ρ (g * h) = ρ g ≫ ρ h)
variable (f : X ⟶ S) (hf : ∀ g : G, ρ g ≫ f = f)

/-- The canonical point of an affine scheme associated to the residue field
of a prime of its global-functions ring. -/
noncomputable def affinePrimeResiduePoint (q : PrimeSpectrum Γ(X, ⊤)) :
    Spec (.of q.asIdeal.ResidueField) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) q.asIdeal.ResidueField)) ≫
    X.isoSpec.inv

/-- The stabilizer of a prime for the global-section action induced by a
right action on an affine scheme. -/
noncomputable abbrev affineSchemePrimeStabilizer
    (q : PrimeSpectrum Γ(X, ⊤)) :=
  letI := schemeGlobalSectionAction G ρ h₁ hcomp
  MulAction.stabilizer G q.asIdeal

/-- The Galois group of the invariant-quotient residue extension associated
to a prime of an affine scheme carrying the induced global-section action. -/
noncomputable abbrev affineSchemePrimeResidueGal
    (q : PrimeSpectrum Γ(X, ⊤)) :=
  letI := schemeGlobalSectionAction G ρ h₁ hcomp
  letI := f.appTop.hom.toAlgebra
  letI : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) :=
    schemeGlobalSectionAction_smulComm G ρ h₁ hcomp f hf
  affineInvariantPrimeResidueGal Γ(S, ⊤) Γ(X, ⊤) G q

/-- On an affine scheme, the residue-field automorphism induced by a prime
stabilizer carries the canonical residue point to its translate by the
corresponding scheme automorphism. -/
theorem affineSchemePrimeResidueStabilizer_point
    (q : PrimeSpectrum Γ(X, ⊤))
    (s : affineSchemePrimeStabilizer G ρ h₁ hcomp q) :
    letI := schemeGlobalSectionAction G ρ h₁ hcomp
    letI := f.appTop.hom.toAlgebra
    letI : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) :=
      schemeGlobalSectionAction_smulComm G ρ h₁ hcomp f hf
    Spec.map (CommRingCat.ofHom
          (affineInvariantPrimeResidueStabilizerEquiv
            Γ(S, ⊤) Γ(X, ⊤) G q s).toRingHom) ≫
        affinePrimeResiduePoint q =
      affinePrimeResiduePoint q ≫ ρ s.val := by
  letI := schemeGlobalSectionAction G ρ h₁ hcomp
  letI := f.appTop.hom.toAlgebra
  letI : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) :=
    schemeGlobalSectionAction_smulComm G ρ h₁ hcomp f hf
  rw [affinePrimeResiduePoint, ← Category.assoc,
    affineInvariantPrimeResidueStabilizer_specMap Γ(S, ⊤) Γ(X, ⊤) G q s]
  simp only [Category.assoc]
  congr 1
  apply (X.isoSpec.comp_inv_eq).2
  rw [Category.assoc, ← Scheme.isoSpec_hom_naturality]
  simp
  rw [Spec.map_inj]
  rfl

/-- Every automorphism of the residue Galois extension carries the canonical
residue point to one of its translates under the original scheme action. -/
theorem affineSchemePrimeResidue_galoisOrbit
    (q : PrimeSpectrum Γ(X, ⊤))
    (g : affineSchemePrimeResidueGal G ρ h₁ hcomp f hf q) :
    letI := schemeGlobalSectionAction G ρ h₁ hcomp
    letI := f.appTop.hom.toAlgebra
    letI : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) :=
      schemeGlobalSectionAction_smulComm G ρ h₁ hcomp f hf
    ∃ s : affineSchemePrimeStabilizer G ρ h₁ hcomp q,
      Spec.map (CommRingCat.ofHom
          (affineInvariantPrimeResidueGalRingEquiv
            Γ(S, ⊤) Γ(X, ⊤) G q g).toRingHom) ≫
          affinePrimeResiduePoint q =
        affinePrimeResiduePoint q ≫ ρ s.val := by
  letI := schemeGlobalSectionAction G ρ h₁ hcomp
  letI := f.appTop.hom.toAlgebra
  letI : SMulCommClass G Γ(S, ⊤) Γ(X, ⊤) :=
    schemeGlobalSectionAction_smulComm G ρ h₁ hcomp f hf
  obtain ⟨s, hs⟩ := exists_affineInvariantPrimeStabilizer_of_galois
    Γ(S, ⊤) Γ(X, ⊤) G q g
  refine ⟨s, ?_⟩
  rw [← hs]
  exact affineSchemePrimeResidueStabilizer_point
    G ρ h₁ hcomp f hf q s

end AffineScheme

end AllCharacteristics
