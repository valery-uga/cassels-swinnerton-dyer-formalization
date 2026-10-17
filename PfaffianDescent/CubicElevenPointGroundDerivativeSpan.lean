import PfaffianDescent.CubicElevenPointKernelScalarExtension

/-! Full interpolation makes the derivatives of a ground-field cubic
ideal basis span all six surface derivatives over the splitting field. -/

noncomputable section
namespace PfaffianDescent

open MvPolynomial Module

universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicElevenPoint_groundKernel_derivativeFamily_spans
    {F E A : Type u} [Field F] [Field E] [Algebra F E]
    [AddCommGroup A] [Module F A] [FiniteDimensional F A]
    (R : homogeneousSubmodule (Fin 4) F 3 →ₗ[F] A)
    (hA : finrank F A ≤ 11) (x : Fin 11 → Fin 4 → E)
    (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet E)
    (hresidue : ∀ i j, (J i j).fst = x (i.castAdd 8) j)
    (hfull : Function.Surjective (cubicElevenPointFullJetRestriction x J))
    (hmem : ∀ q, R q = 0 → cubicElevenPointValueRestriction x
      (voisinDegreeTenSelectedAvoidance_mapCubicSection (L := E) q) = 0)
    (B : Basis (Fin 9) F R.ker) :
    Submodule.span E (Set.range (fun k : Fin 9 => fun i : Fin 3 =>
      (aeval (J i) ((B k).1.1.map (algebraMap F E))).snd)) = ⊤ := by
  let D : homogeneousSubmodule (Fin 4) E 3 →ₗ[E] (Fin 3 → Fin 2 → E) :=
    LinearMap.pi fun i => (TrivSqZeroExt.sndHom E (Fin 2 → E)).comp
      ((aeval (J i)).toLinearMap.domRestrict _)
  have hvalues := cubicElevenPointValueRestriction_surjective_of_fullJets x J hresidue hfull
  have hspan := cubicElevenPoint_groundKernel_basis_spans_split_kernel R hA x hvalues hmem B
  have hderiv := cubicElevenPointIdealFirstDerivativeRestriction_surjective_of_fullJets
    x J hresidue hfull
  have hmap := congrArg (Submodule.map D) hspan
  rw [Submodule.map_span, ← Set.range_comp', ← LinearMap.range_domRestrict] at hmap
  have hD : Function.Surjective (D.domRestrict (cubicElevenPointValueRestriction x).ker) := hderiv
  rw [LinearMap.range_eq_top.mpr hD] at hmap
  exact hmap

end PfaffianDescent
