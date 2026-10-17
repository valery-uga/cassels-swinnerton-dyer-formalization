import AllCharacteristics.CyclePushforward
import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks

/-!
# Residue fields along a section

At every point of the base, a section induces an isomorphism on residue
fields.  This identifies the residue field of the image of a rational point
with the original ground field when applying invariant-quotient residue
theory.
-/

open AlgebraicGeometry CategoryTheory

namespace AllCharacteristics
universe u

/-- A section induces an isomorphism on the residue field at every base
point. -/
theorem isIso_residueFieldMap_of_section
    {X S : Scheme.{u}} (f : X ⟶ S) (c : S ⟶ X)
    (hc : c ≫ f = 𝟙 S) (s : S) :
    IsIso (c.residueFieldMap s) := by
  haveI : SurjectiveOnStalks (c ≫ f) := by
    rw [hc]
    infer_instance
  haveI : SurjectiveOnStalks c := SurjectiveOnStalks.of_comp c f
  exact isIso_residueFieldMap_of_surjectiveOnStalks c s

/-- The scheme-theoretic residue field at the unique point of the spectrum
of a field is canonically isomorphic to that field. -/
noncomputable def specFieldClosedPointResidueIso
    (K : Type u) [Field K] :
    (Spec (.of K)).residueField (IsLocalRing.closedPoint K) ≃+* K :=
  (Scheme.Spec.residueFieldIso (.of K)
      (IsLocalRing.closedPoint K)).commRingCatIsoToRingEquiv.trans
    (Ideal.algEquivResidueFieldOfField
      (IsLocalRing.closedPoint K).asIdeal).symm.toRingEquiv

/-- The inverse of the canonical residue-field identification gives the
standard residue point of the spectrum of a field. -/
theorem specFieldClosedPointResidueIso_symm_specMap
    (K : Type u) [Field K] :
    Spec.map (CommRingCat.ofHom
      (specFieldClosedPointResidueIso K).symm.toRingHom) =
      (Spec (.of K)).fromSpecResidueField (IsLocalRing.closedPoint K) := by
  change Spec.map (CommRingCat.ofHom (algebraMap K
      (IsLocalRing.closedPoint K).asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (.of K)
          (IsLocalRing.closedPoint K)).inv) = _
  rw [Spec.map_comp]
  exact Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField
    (.of K) (IsLocalRing.closedPoint K)

/-- The residue field at the image of a field-valued section is canonically
isomorphic to the ground field. -/
noncomputable def sectionResidueFieldIso
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (c : Spec (.of K) ⟶ X)
    (hc : c ≫ f = 𝟙 _) :
    X.residueField (c (IsLocalRing.closedPoint K)) ≃+* K := by
  letI : IsIso (c.residueFieldMap (IsLocalRing.closedPoint K)) :=
    isIso_residueFieldMap_of_section f c hc _
  exact
    (asIso (c.residueFieldMap
      (IsLocalRing.closedPoint K))).commRingCatIsoToRingEquiv.trans
        (specFieldClosedPointResidueIso K)

/-- The inverse residue-field identification followed on spectra is exactly
the structure morphism of the residue point. -/
theorem sectionResidueFieldIso_symm_specMap
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (c : Spec (.of K) ⟶ X)
    (hc : c ≫ f = 𝟙 _) :
    Spec.map (CommRingCat.ofHom
      (sectionResidueFieldIso f c hc).symm.toRingHom) =
      X.fromSpecResidueField (c (IsLocalRing.closedPoint K)) ≫ f := by
  let s : Spec (.of K) := IsLocalRing.closedPoint K
  letI : IsIso (c.residueFieldMap s) :=
    isIso_residueFieldMap_of_section f c hc s
  let r := Spec.map (inv (c.residueFieldMap s))
  have hnat := Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField c s
  have hinvNat : r ≫ (Spec (.of K)).fromSpecResidueField s ≫ c =
      X.fromSpecResidueField (c s) := by
    calc
      r ≫ (Spec (.of K)).fromSpecResidueField s ≫ c =
          r ≫ (Spec.map (c.residueFieldMap s) ≫
            X.fromSpecResidueField (c s)) := by rw [hnat]
      _ = (r ≫ Spec.map (c.residueFieldMap s)) ≫
          X.fromSpecResidueField (c s) := Category.assoc _ _ _ |>.symm
      _ = X.fromSpecResidueField (c s) := by
        dsimp only [r]
        rw [← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id,
          Category.id_comp]
  unfold sectionResidueFieldIso
  change Spec.map
      ((specFieldClosedPointResidueIso K).symm.toCommRingCatIso.hom ≫
        (asIso (c.residueFieldMap s)).inv) = _
  rw [Spec.map_comp]
  have hs := specFieldClosedPointResidueIso_symm_specMap K
  change Spec.map
      (specFieldClosedPointResidueIso K).symm.toCommRingCatIso.hom =
    (Spec (.of K)).fromSpecResidueField s at hs
  rw [hs]
  change r ≫ (Spec (.of K)).fromSpecResidueField s = _
  calc
    r ≫ (Spec (.of K)).fromSpecResidueField s =
        (r ≫ (Spec (.of K)).fromSpecResidueField s ≫ c) ≫ f := by
      simp only [Category.assoc, hc, Category.comp_id]
    _ = X.fromSpecResidueField (c s) ≫ f := by rw [hinvNat]

/-- For an affine target, identify the ideal-theoretic residue field of the
prime selected by a section with the ground field.  This is the form used by
finite invariant-quotient residue theory. -/
noncomputable def sectionIdealResidueFieldIso
    {K B : Type u} [Field K] [CommRing B]
    (f : Spec (.of B) ⟶ Spec (.of K))
    (c : Spec (.of K) ⟶ Spec (.of B))
    (hc : c ≫ f = 𝟙 _) :
    let q : PrimeSpectrum B := c (IsLocalRing.closedPoint K)
    letI : q.asIdeal.IsPrime := q.isPrime
    q.asIdeal.ResidueField ≃+* K := by
  let q : PrimeSpectrum B := c (IsLocalRing.closedPoint K)
  letI : q.asIdeal.IsPrime := q.isPrime
  exact (Scheme.Spec.residueFieldIso (.of B)
      q).symm.commRingCatIsoToRingEquiv.trans
    (sectionResidueFieldIso f c hc)

/-- Identify the residue field of any prime proved equal to the point selected
by an affine section with the ground field.  Passing through scheme residue
fields makes compatibility with the canonical residue-point morphism
explicit. -/
noncomputable def sectionIdealResidueFieldIsoOfPointEq
    {K B : Type u} [Field K] [CommRing B]
    (f : Spec (.of B) ⟶ Spec (.of K))
    (c : Spec (.of K) ⟶ Spec (.of B))
    (hc : c ≫ f = 𝟙 _)
    (p : PrimeSpectrum B)
    (hp : p = c (IsLocalRing.closedPoint K)) :
    p.asIdeal.ResidueField ≃+* K :=
  let r : PrimeSpectrum B := c (IsLocalRing.closedPoint K)
  let eIdeal : p.asIdeal.ResidueField ≃+*
      (Spec (.of B)).residueField p :=
    (Scheme.Spec.residueFieldIso (.of B) p).symm.commRingCatIsoToRingEquiv
  let ePoint : (Spec (.of B)).residueField p ≃+*
      (Spec (.of B)).residueField r :=
    ((Spec (.of B)).residueFieldCongr hp).commRingCatIsoToRingEquiv
  eIdeal.trans (ePoint.trans (sectionResidueFieldIso f c hc))

/-- The transported base map for a prime equal to a section point is exactly
its canonical residue point followed by the affine structure morphism. -/
theorem sectionIdealResidueFieldIsoOfPointEq_symm_specMap
    {K B : Type u} [Field K] [CommRing B]
    (f : Spec (.of B) ⟶ Spec (.of K))
    (c : Spec (.of K) ⟶ Spec (.of B))
    (hc : c ≫ f = 𝟙 _)
    (p : PrimeSpectrum B)
    (hp : p = c (IsLocalRing.closedPoint K)) :
    Spec.map (CommRingCat.ofHom
      (sectionIdealResidueFieldIsoOfPointEq f c hc p hp).symm.toRingHom) =
      Spec.map (CommRingCat.ofHom
        (algebraMap B p.asIdeal.ResidueField)) ≫ f := by
  let r : PrimeSpectrum B := c (IsLocalRing.closedPoint K)
  let eSpec := Scheme.Spec.residueFieldIso (.of B) p
  let ePoint := (Spec (.of B)).residueFieldCongr hp
  have hsec := sectionResidueFieldIso_symm_specMap f c hc
  change Spec.map (sectionResidueFieldIso f c hc).symm.toCommRingCatIso.hom =
    (Spec (.of B)).fromSpecResidueField r ≫ f at hsec
  have hcongr :=
    (Spec (.of B)).residueFieldCongr_fromSpecResidueField hp.symm
  change Spec.map ePoint.inv ≫ (Spec (.of B)).fromSpecResidueField r =
    (Spec (.of B)).fromSpecResidueField p at hcongr
  have hres := Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField
    (.of B) p
  have hideal : Spec.map eSpec.hom ≫
      (Spec (.of B)).fromSpecResidueField p =
      Spec.map (CommRingCat.ofHom
        (algebraMap B p.asIdeal.ResidueField)) := by
    calc
      Spec.map eSpec.hom ≫ (Spec (.of B)).fromSpecResidueField p =
          Spec.map eSpec.hom ≫ (Spec.map eSpec.inv ≫
            Spec.map (CommRingCat.ofHom
              (algebraMap B p.asIdeal.ResidueField))) := by rw [hres]
      _ = (Spec.map eSpec.hom ≫ Spec.map eSpec.inv) ≫
            Spec.map (CommRingCat.ofHom
              (algebraMap B p.asIdeal.ResidueField)) :=
        Category.assoc _ _ _ |>.symm
      _ = _ := by rw [← Spec.map_comp, eSpec.inv_hom_id,
        Spec.map_id, Category.id_comp]
  unfold sectionIdealResidueFieldIsoOfPointEq
  change Spec.map
      ((sectionResidueFieldIso f c hc).symm.toCommRingCatIso.hom ≫
        ePoint.inv ≫ eSpec.hom) = _
  rw [Spec.map_comp
    (sectionResidueFieldIso f c hc).symm.toCommRingCatIso.hom
    (ePoint.inv ≫ eSpec.hom)]
  rw [Spec.map_comp ePoint.inv eSpec.hom]
  calc
    Spec.map eSpec.hom ≫ Spec.map ePoint.inv ≫
        Spec.map (sectionResidueFieldIso f c hc).symm.toCommRingCatIso.hom =
      Spec.map eSpec.hom ≫ Spec.map ePoint.inv ≫
        ((Spec (.of B)).fromSpecResidueField r ≫ f) := by rw [hsec]
    _ = Spec.map eSpec.hom ≫
        (Spec.map ePoint.inv ≫
          (Spec (.of B)).fromSpecResidueField r) ≫ f := by
      simp only [Category.assoc]
    _ = Spec.map eSpec.hom ≫
        (Spec (.of B)).fromSpecResidueField p ≫ f :=
      congrArg (fun m => (Spec.map eSpec.hom ≫ m) ≫ f) hcongr
    _ = Spec.map (CommRingCat.ofHom
          (algebraMap B p.asIdeal.ResidueField)) ≫ f :=
      congrArg (· ≫ f) hideal

/-- For an affine section, the transported ground-field map into the ideal
residue field is exactly the composite of the canonical residue point with
the structure morphism. -/
theorem sectionIdealResidueFieldIso_symm_specMap
    {K B : Type u} [Field K] [CommRing B]
    (f : Spec (.of B) ⟶ Spec (.of K))
    (c : Spec (.of K) ⟶ Spec (.of B))
    (hc : c ≫ f = 𝟙 _) :
    let q : PrimeSpectrum B := c (IsLocalRing.closedPoint K)
    let e := sectionIdealResidueFieldIso f c hc
    Spec.map (CommRingCat.ofHom e.symm.toRingHom) =
      Spec.map (CommRingCat.ofHom
        (algebraMap B q.asIdeal.ResidueField)) ≫ f := by
  let q : PrimeSpectrum B := c (IsLocalRing.closedPoint K)
  let e := Scheme.Spec.residueFieldIso (.of B) q
  have hscheme := sectionResidueFieldIso_symm_specMap f c hc
  change Spec.map (sectionResidueFieldIso f c hc).symm.toCommRingCatIso.hom =
    (Spec (.of B)).fromSpecResidueField q ≫ f at hscheme
  have hres := Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField
    (.of B) q
  unfold sectionIdealResidueFieldIso
  change Spec.map
      ((sectionResidueFieldIso f c hc).symm.toCommRingCatIso.hom ≫ e.hom) = _
  rw [Spec.map_comp, hscheme]
  calc
    Spec.map e.hom ≫
        ((Spec (.of B)).fromSpecResidueField q ≫ f) =
      (Spec.map e.hom ≫ (Spec (.of B)).fromSpecResidueField q) ≫ f :=
        Category.assoc _ _ _ |>.symm
    _ = Spec.map (CommRingCat.ofHom
          (algebraMap B q.asIdeal.ResidueField)) ≫ f := by
      congr 1
      calc
        Spec.map e.hom ≫ (Spec (.of B)).fromSpecResidueField q =
            Spec.map e.hom ≫ (Spec.map e.inv ≫
              Spec.map (CommRingCat.ofHom
                (algebraMap B q.asIdeal.ResidueField))) := by rw [hres]
        _ = (Spec.map e.hom ≫ Spec.map e.inv) ≫
              Spec.map (CommRingCat.ofHom
                (algebraMap B q.asIdeal.ResidueField)) :=
          Category.assoc _ _ _ |>.symm
        _ = _ := by rw [← Spec.map_comp, e.inv_hom_id,
          Spec.map_id, Category.id_comp]

end AllCharacteristics
