import AllCharacteristics.CubicGraphLineDifferential
import AllCharacteristics.CubicLineCoordinateFieldDescent
import AllCharacteristics.CubicGenericLineExclusion

/-! Actual graph containment and geometric nonsingularity construct rigidity;
rigidity constructs descent of the entire graph coordinate field. -/

noncomputable section
namespace AllCharacteristics

open PfaffianDescent
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- Every contained graph line's generated coordinate field over an
algebraically closed ground field is the ground field. This uses the actual
cubic equation and its geometric nonsingularity, with no Fano finiteness or
generic tangent-section hypothesis. -/
theorem cubicGraphLine_generated_coordinate_field_descends
    [IsAlgClosed K] (c : Cubic K 4) (a : Fin 4 → L)
    (hgen : IntermediateField.adjoin K (Set.range a) = ⊤)
    (hline : ∀ t : K, (c.map (algebraMap K L)).eval
      (algebraMap K L t • cubicGraphLineSlope a + cubicGraphLineBase a) = 0)
    (hsmooth : ∀ (M : Type u) [Field M] (f : L →+* M) (x : Fin 4 → M),
      x ≠ 0 → ((c.map (algebraMap K L)).map f).eval x = 0 →
      ∃ d, ((c.map (algebraMap K L)).map f).mixed x d ≠ 0) :
    Function.Bijective (algebraMap K L) := by
  have hcoeff := cubicGraphLine_four_coefficients_eq_zero c a hline
  have hcop := cubicGraphLine_normalPolynomials_isCoprime_of_geometric_nonsingularity
    (c.map (algebraMap K L)) a hcoeff hsmooth
  have hs0 : cubicGraphLineSlope a ≠ 0 := by
    intro hzero
    have h0 := congrFun hzero 0
    simpa [cubicGraphLineSlope] using h0
  have hsmooth0 : ∃ d, (c.map (algebraMap K L)).mixed (cubicGraphLineSlope a) d ≠ 0 := by
    have hid : (c.map (algebraMap K L)).map (RingHom.id L) = c.map (algebraMap K L) := by
      funext j
      rfl
    simpa only [hid] using
      hsmooth L (RingHom.id L) (cubicGraphLineSlope a) hs0 hcoeff.1
  have hinfty := cubicGraphLine_nonzero_normal_at_infinity
    (c.map (algebraMap K L)) a hcoeff.1 hcoeff.2.1 hsmooth0
  exact cubicLine_fieldCoordinates_descend_of_scalar_rigidity a hgen
    (fun D => cubicGraphLine_scalar_rigidity_of_normal_derivatives c a hline hcop hinfty D)

/-- Consequently a generic vector with independent homogeneous coordinates
cannot belong to any contained graph line represented over its own generated
coordinate field. -/
theorem cubicGeneric_not_on_contained_graph_over_generated_field
    [IsAlgClosed K] {E : Type u} [Field E] [Algebra K E]
    (c : Cubic K 4) (a : Fin 4 → L)
    (hgen : IntermediateField.adjoin K (Set.range a) = ⊤)
    (hline : ∀ t : K, (c.map (algebraMap K L)).eval
      (algebraMap K L t • cubicGraphLineSlope a + cubicGraphLineBase a) = 0)
    (hsmooth : ∀ (M : Type u) [Field M] (f : L →+* M) (x : Fin 4 → M),
      x ≠ 0 → ((c.map (algebraMap K L)).map f).eval x = 0 →
      ∃ d, ((c.map (algebraMap K L)).map f).mixed x d ≠ 0)
    (e : L →ₐ[K] E) (x : Fin 4 → E) (hx : LinearIndependent K x) :
    x 2 ≠ e (a 0) * x 0 + e (a 1) * x 1 := by
  have hdesc := cubicGraphLine_generated_coordinate_field_descends c a hgen hline hsmooth
  obtain ⟨a₀, ha₀⟩ := hdesc.surjective (a 0)
  obtain ⟨a₁, ha₁⟩ := hdesc.surjective (a 1)
  rw [← ha₀, ← ha₁, e.commutes, e.commutes]
  exact cubic_generic_coordinates_not_on_ground_graph_line x hx a₀ a₁

/-- The own-coordinate field is constructed internally. Thus every contained
graph line over ANY extension of an algebraically closed field descends to
the ground field. All smoothness and containment statements concern the
original cubic equation. -/
theorem cubicGraphLine_coordinates_descend
    [IsAlgClosed K] (c : Cubic K 4) (a : Fin 4 → L)
    (hline : ∀ t : K, (c.map (algebraMap K L)).eval
      (algebraMap K L t • cubicGraphLineSlope a + cubicGraphLineBase a) = 0)
    (hsmooth : ∀ (M : Type u) [Field M] (f : K →+* M) (x : Fin 4 → M),
      x ≠ 0 → (c.map f).eval x = 0 → ∃ d, (c.map f).mixed x d ≠ 0) :
    ∃ b : Fin 4 → K, ∀ i, algebraMap K L (b i) = a i := by
  let F := cubicLineCoordinateSubfield (K := K) a
  let aF : Fin 4 → F := cubicLineCoordinateInSubfield (K := K) a
  have hmap : (c.map (algebraMap K F)).map F.val.toRingHom = c.map (algebraMap K L) := by
    funext j
    exact F.val.commutes (c j)
  have hlineF : ∀ t : K, (c.map (algebraMap K F)).eval
      (algebraMap K F t • cubicGraphLineSlope aF + cubicGraphLineBase aF) = 0 := by
    intro t
    apply F.val.injective
    rw [map_zero, ← Cubic.eval_map, hmap]
    have hpoint :
        (fun i => F.val.toRingHom ((algebraMap K F t • cubicGraphLineSlope aF + cubicGraphLineBase aF) i)) =
        algebraMap K L t • cubicGraphLineSlope a + cubicGraphLineBase a := by
      have ht : F.val.toRingHom (algebraMap K F t) = algebraMap K L t := F.val.commutes t
      have hs : (fun i => F.val.toRingHom (cubicGraphLineSlope aF i)) = cubicGraphLineSlope a :=
        cubicGraphLineSlope_map F.val.toRingHom aF
      have hb : (fun i => F.val.toRingHom (cubicGraphLineBase aF i)) = cubicGraphLineBase a :=
        cubicGraphLineBase_map F.val.toRingHom aF
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
      rw [ht, congrFun hs i, congrFun hb i]
    rw [hpoint]
    exact hline t
  have hsmoothF : ∀ (M : Type u) [Field M] (f : F →+* M) (x : Fin 4 → M),
      x ≠ 0 → ((c.map (algebraMap K F)).map f).eval x = 0 →
      ∃ d, ((c.map (algebraMap K F)).map f).mixed x d ≠ 0 := by
    intro M _ f x hx hcx
    exact hsmooth M (f.comp (algebraMap K F)) x hx hcx
  have hdesc : Function.Bijective (algebraMap K F) := cubicGraphLine_generated_coordinate_field_descends c aF
    (cubicLineCoordinateInSubfield_adjoin_eq_top a) hlineF hsmoothF
  choose b hb using fun i : Fin 4 => hdesc.surjective (aF i)
  refine ⟨b, fun i => ?_⟩
  calc
    algebraMap K L (b i) = F.val (algebraMap K F (b i)) := (F.val.commutes _).symm
    _ = F.val (aF i) := congrArg F.val (hb i)
    _ = a i := rfl

/-- A genuine generic coordinate vector cannot lie on any contained graph
line over its own field. There is no line-descent, rigidity, coprimeness, or
field-generation premise in this endpoint. -/
theorem cubicGeneric_not_on_contained_graph
    [IsAlgClosed K] (c : Cubic K 4) (x a : Fin 4 → L)
    (hx : LinearIndependent K x)
    (hline : ∀ t : K, (c.map (algebraMap K L)).eval
      (algebraMap K L t • cubicGraphLineSlope a + cubicGraphLineBase a) = 0)
    (hsmooth : ∀ (M : Type u) [Field M] (f : K →+* M) (y : Fin 4 → M),
      y ≠ 0 → (c.map f).eval y = 0 → ∃ d, (c.map f).mixed y d ≠ 0) :
    x 2 ≠ a 0 * x 0 + a 1 * x 1 := by
  obtain ⟨b, hb⟩ := cubicGraphLine_coordinates_descend c a hline hsmooth
  rw [← hb 0, ← hb 1]
  exact cubic_generic_coordinates_not_on_ground_graph_line x hx (b 0) (b 1)

end AllCharacteristics
