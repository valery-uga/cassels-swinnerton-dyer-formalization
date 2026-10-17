import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualKernelCover

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_pullback_snd_kernel
    {X Z U : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (v : U ⟶ X) :
    (pullback.snd i v).ker = i.ker.comap v := by
  rw [← Scheme.Hom.ker_comp_of_isIso (pullbackSymmetry v i).hom,
    pullbackSymmetry_hom_comp_snd,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

theorem cubicClosedPointSerreFiniteZeroResidual_ideal_eq_of_affine_pullbacks
    {X : Scheme.{u}} (I J : X.IdealSheafData)
    {ι : Type*} (U : ι → X.affineOpens) (hU : ⨆ k, (U k).1 = ⊤)
    (h : ∀ k, I.comap (U k).1.ι = J.comap (U k).1.ι) : I = J := by
  have he := cubicClosedPointSerreFiniteZeroResidual_kernel_eq_of_affine_pullbacks
    I.subschemeι J.subschemeι U hU (fun k => by
      rw [cubicClosedPointSerreFiniteZeroResidual_pullback_snd_kernel,
        cubicClosedPointSerreFiniteZeroResidual_pullback_snd_kernel,
        Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
      exact h k)
  simpa using he

end PfaffianDescent
