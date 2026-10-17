import PfaffianDescent.CubicPointTraceFieldBaseChangeDiagonal

/-! # The actual rational point above a closed residue-field point

The lift is the diagonal of the actual scalar-extended point fibre. The
tensor-spectrum coordinate comparison proves this, including its two
projections and its closed and open immersion properties.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace PfaffianDescent
universe u

section
variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- The actual diagonal in the base change of the field point to its own
residue field. -/
def cubicPointTraceFieldBaseChangeDiagonalPoint :
    Spec (.of L) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
        (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  pullback.lift (𝟙 _) (𝟙 _) (by simp)

@[reassoc (attr := simp)]
theorem cubicPointTraceFieldBaseChangeDiagonalPoint_fst :
    cubicPointTraceFieldBaseChangeDiagonalPoint K L ≫ pullback.fst _ _ = 𝟙 _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem cubicPointTraceFieldBaseChangeDiagonalPoint_snd :
    cubicPointTraceFieldBaseChangeDiagonalPoint K L ≫ pullback.snd _ _ = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- Multiplication on the tensor ring defines precisely the actual diagonal
of the scalar-extended point, through the canonical affine fibre isomorphism. -/
theorem cubicPointTraceFieldBaseChangeDiagonalPoint_eq_tensor :
    cubicPointTraceFieldBaseChangeDiagonalPoint K L =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lmul' K (S := L)).toRingHom) ≫
        (pullbackSpecIso K L L).inv := by
  apply pullback.hom_ext
  · rw [cubicPointTraceFieldBaseChangeDiagonalPoint_fst, Category.assoc,
      pullbackSpecIso_inv_fst, ← Spec.map_comp]
    change 𝟙 _ = Spec.map (CommRingCat.ofHom
      ((Algebra.TensorProduct.lmul' K (S := L)).toRingHom.comp
        Algebra.TensorProduct.includeLeftRingHom))
    have h : (Algebra.TensorProduct.lmul' K (S := L)).toRingHom.comp
        Algebra.TensorProduct.includeLeftRingHom = RingHom.id L := by
      ext a
      simp
    rw [h]
    exact (Spec.map_id _).symm
  · rw [cubicPointTraceFieldBaseChangeDiagonalPoint_snd, Category.assoc,
      pullbackSpecIso_inv_snd, ← Spec.map_comp]
    change 𝟙 _ = Spec.map (CommRingCat.ofHom
      ((Algebra.TensorProduct.lmul' K (S := L)).toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := L)).toRingHom))
    have h : (Algebra.TensorProduct.lmul' K (S := L)).toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := L)).toRingHom =
        RingHom.id L := by
      ext a
      simp
    rw [h]
    exact (Spec.map_id _).symm

instance cubicPointTraceFieldBaseChangeDiagonalPoint_isClosedImmersion :
    IsClosedImmersion (cubicPointTraceFieldBaseChangeDiagonalPoint K L) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.lmul' K (S := L)).toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ (fun a => ⟨a ⊗ₜ[K] 1, by simp⟩)
  rw [cubicPointTraceFieldBaseChangeDiagonalPoint_eq_tensor]
  infer_instance

instance cubicPointTraceFieldBaseChangeDiagonalPoint_isOpenImmersion
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    IsOpenImmersion (cubicPointTraceFieldBaseChangeDiagonalPoint K L) := by
  let : Algebra.FormallyUnramified K L :=
    Algebra.FormallyUnramified.of_isSeparable K L
  rw [cubicPointTraceFieldBaseChangeDiagonalPoint_eq_tensor]
  infer_instance

variable {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
  (i : Spec (.of L) ⟶ X)
  (hi : i ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- The actual residue-field rational lift of the original point. -/
def cubicPointTraceFieldBaseChangeRationalPoint :
    Spec (.of L) ⟶ schemeBaseChangeToField (L := L) X p :=
  pullback.lift i (𝟙 _) (by simpa using hi)

@[reassoc (attr := simp)]
theorem cubicPointTraceFieldBaseChangeRationalPoint_fst :
    cubicPointTraceFieldBaseChangeRationalPoint K L p i hi ≫
      pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L))) = i :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem cubicPointTraceFieldBaseChangeRationalPoint_snd :
    cubicPointTraceFieldBaseChangeRationalPoint K L p i hi ≫
      pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap K L))) = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The rational lift factors through the actual scalar-extended original
closed point by its diagonal component. -/
theorem cubicPointTraceFieldBaseChangeRationalPoint_eq_diagonal :
    cubicPointTraceFieldBaseChangeRationalPoint K L p i hi =
      cubicPointTraceFieldBaseChangeDiagonalPoint K L ≫
        finitePointBaseChangeToAmbient (L := L) p i hi := by
  apply pullback.hom_ext
  · simp
  · simp

instance cubicPointTraceFieldBaseChangeRationalPoint_isClosedImmersion
    [IsClosedImmersion i] :
    IsClosedImmersion (cubicPointTraceFieldBaseChangeRationalPoint K L p i hi) := by
  rw [cubicPointTraceFieldBaseChangeRationalPoint_eq_diagonal]
  infer_instance

end
end PfaffianDescent
