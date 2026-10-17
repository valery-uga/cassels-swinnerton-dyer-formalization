import AllCharacteristics.ClosedPointAlgebra
import AllCharacteristics.ProperCyclePushforward
import AllCharacteristics.SectionResidueField

/-!
# Residue embeddings of finite field-valued points

A point valued in a finite extension of the ground field has closed image on
a separated scheme.  Its map on residue fields gives a canonical embedding
of the image residue field into the coefficient field.  This file records
the factorization and its compatibility with Galois precomposition.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AllCharacteristics

universe u

variable {K E : Type u} [Field K] [Field E] [Algebra K E]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of K))

/-- The residue-field ring map induced by a field-valued point, with the
residue field of `Spec E` identified canonically with `E`. -/
noncomputable def fieldPointResidueRingHom
    (a : Spec (.of E) ⟶ X) :
    X.residueField (a (IsLocalRing.closedPoint E)) →+* E :=
  (specFieldClosedPointResidueIso E).toRingHom.comp
    (a.residueFieldMap (IsLocalRing.closedPoint E)).hom

/-- The residue embedding followed by the canonical residue point recovers
the original field-valued point. -/
theorem fieldPointResidueRingHom_spec
    (a : Spec (.of E) ⟶ X) :
    Spec.map (CommRingCat.ofHom (fieldPointResidueRingHom a)) ≫
        X.fromSpecResidueField (a (IsLocalRing.closedPoint E)) = a := by
  let s : Spec (.of E) := IsLocalRing.closedPoint E
  let e := specFieldClosedPointResidueIso E
  change Spec.map (a.residueFieldMap s ≫
      e.toCommRingCatIso.hom) ≫
      X.fromSpecResidueField (a s) = a
  rw [Spec.map_comp, Category.assoc,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  have hs := specFieldClosedPointResidueIso_symm_specMap E
  change Spec.map (CommRingCat.ofHom e.symm.toRingHom) =
    (Spec (.of E)).fromSpecResidueField s at hs
  have hs' : Spec.map e.toCommRingCatIso.inv =
      (Spec (.of E)).fromSpecResidueField s := hs
  rw [← hs']
  have heid : Spec.map e.toCommRingCatIso.hom ≫
      Spec.map e.toCommRingCatIso.inv = 𝟙 _ := by
    rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  rw [← Category.assoc, heid, Category.id_comp]

/-- The residue embedding is an algebra homomorphism when the field-valued
point lies over the given ground-field extension. -/
noncomputable def fieldPointResidueAlgHom
    (a : Spec (.of E) ⟶ X)
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K E))) :
    let x := a (IsLocalRing.closedPoint E)
    letI := pointAlgebra f x
    X.residueField x →ₐ[K] E := by
  let x := a (IsLocalRing.closedPoint E)
  letI : Algebra K (X.residueField x) := pointAlgebra f x
  let e := fieldPointResidueRingHom a
  refine { e with commutes' := ?_ }
  have he : CommRingCat.ofHom (algebraMap K (X.residueField x)) ≫
      CommRingCat.ofHom e = CommRingCat.ofHom (algebraMap K E) := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    calc
      Spec.map (CommRingCat.ofHom e) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap K (X.residueField x))) =
        Spec.map (CommRingCat.ofHom e) ≫
          (X.fromSpecResidueField x ≫ f) := by
            rw [pointAlgebra_spec f x]
      _ = a ≫ f := by
        rw [← Category.assoc, fieldPointResidueRingHom_spec a]
      _ = Spec.map (CommRingCat.ofHom (algebraMap K E)) := ha
  intro r
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom he) r

/-- A finite field-valued point on a separated scheme has a closed image
point. -/
noncomputable def finiteFieldPointClosedPoint
    [Module.Finite K E] [IsSeparated f]
    (a : Spec (.of E) ⟶ X)
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K E))) :
    closedPoints X := by
  haveI : IsFinite (a ≫ f) := by
    rw [ha]
    exact (IsFinite.SpecMap_iff _).mpr
      (RingHom.finite_algebraMap.mpr inferInstance)
  letI : IsFinite a := IsFinite.of_comp a f
  exact universallyClosedPointMap a
    ⟨IsLocalRing.closedPoint E,
      IsLocalRing.isClosed_singleton_closedPoint E⟩

@[simp]
theorem finiteFieldPointClosedPoint_val
    [Module.Finite K E] [IsSeparated f]
    (a : Spec (.of E) ⟶ X)
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K E))) :
    (finiteFieldPointClosedPoint f a ha).1 =
      a (IsLocalRing.closedPoint E) := rfl

/-- The residue embedding, retargeted along a specified equality of the
image point. -/
noncomputable def fieldPointResidueAlgHomAt
    (a : Spec (.of E) ⟶ X)
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K E)))
    (x : X) (hx : a (IsLocalRing.closedPoint E) = x) :
    letI := pointAlgebra f x
    X.residueField x →ₐ[K] E := by
  subst x
  exact fieldPointResidueAlgHom f a ha

/-- The retargeted residue embedding retains the canonical factorization of
the field-valued point. -/
theorem fieldPointResidueAlgHomAt_spec
    (a : Spec (.of E) ⟶ X)
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K E)))
    (x : X) (hx : a (IsLocalRing.closedPoint E) = x) :
    letI := pointAlgebra f x
    Spec.map (CommRingCat.ofHom
        (fieldPointResidueAlgHomAt f a ha x hx).toRingHom) ≫
      X.fromSpecResidueField x = a := by
  subst x
  exact fieldPointResidueRingHom_spec a

/-- Precomposing a field point by a ground-field automorphism postcomposes
its residue embedding by the same automorphism. -/
theorem fieldPointResidueAlgHomAt_precomp
    (x : closedPoints X)
    (a b : Spec (.of E) ⟶ X)
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K E)))
    (hb : b ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K E)))
    (hax : a (IsLocalRing.closedPoint E) = x.1)
    (hbx : b (IsLocalRing.closedPoint E) = x.1)
    (g : E ≃ₐ[K] E)
    (hg : Spec.map (CommRingCat.ofHom g.toRingHom) ≫ a = b) :
    letI := pointAlgebra f x.1
    fieldPointResidueAlgHomAt f b hb x.1 hbx =
      g.toAlgHom.comp (fieldPointResidueAlgHomAt f a ha x.1 hax) := by
  letI : Algebra K (X.residueField x.1) := pointAlgebra f x.1
  haveI : IsClosedImmersion (X.fromSpecResidueField x.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp x.2
  apply AlgHom.ext
  intro r
  have hspec : Spec.map (CommRingCat.ofHom
        (fieldPointResidueAlgHomAt f b hb x.1 hbx).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (g.toAlgHom.comp
          (fieldPointResidueAlgHomAt f a ha x.1 hax)).toRingHom) := by
    apply (cancel_mono (X.fromSpecResidueField x.1)).mp
    rw [fieldPointResidueAlgHomAt_spec f b hb x.1 hbx]
    change b = Spec.map
      (CommRingCat.ofHom
          (fieldPointResidueAlgHomAt f a ha x.1 hax).toRingHom ≫
        CommRingCat.ofHom g.toRingHom) ≫
          X.fromSpecResidueField x.1
    rw [Spec.map_comp]
    rw [Category.assoc, fieldPointResidueAlgHomAt_spec f a ha x.1 hax]
    exact hg.symm
  have hr := Spec.map_injective hspec
  exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom hr) r

end AllCharacteristics
