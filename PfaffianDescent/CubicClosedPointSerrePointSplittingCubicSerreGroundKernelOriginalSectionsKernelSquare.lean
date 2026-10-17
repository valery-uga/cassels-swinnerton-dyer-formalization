import PfaffianDescent.CubicClosedPointSerrePointSplittingKernelTransport

noncomputable section
namespace PfaffianDescent
universe u

/-- Kernel equivalence of a literal commuting square whose source and target
maps are actual linear equivalences. -/
def pointSplittingGroundKernel_equivOfSourceSquare
    {E U V W Z : Type u} [Field E]
    [AddCommGroup U] [Module E U] [AddCommGroup V] [Module E V]
    [AddCommGroup W] [Module E W] [AddCommGroup Z] [Module E Z]
    (R : U →ₗ[E] V) (T : W →ₗ[E] Z)
    (A : U ≃ₗ[E] W) (B : V ≃ₗ[E] Z)
    (h : B.toLinearMap.comp (R.comp A.symm.toLinearMap) = T) :
    R.ker ≃ₗ[E] T.ker := by
  let f : R.ker →ₗ[E] T.ker :=
    { toFun := fun x => ⟨A x, by
        change T (A x) = 0
        have hx : B (R (A.symm (A x))) = T (A x) := DFunLike.congr_fun h (A x)
        rw [A.symm_apply_apply, x.property, B.map_zero] at hx
        exact hx.symm⟩
      map_add' := fun x y => Subtype.ext (A.map_add x y)
      map_smul' := fun c x => Subtype.ext (A.map_smul c x) }
  let g : T.ker →ₗ[E] R.ker :=
    { toFun := fun x => ⟨A.symm x, by
        change R (A.symm x) = 0
        apply B.injective
        have hx : B (R (A.symm x)) = T x := DFunLike.congr_fun h (x : W)
        exact hx.trans (x.property.trans B.map_zero.symm)⟩
      map_add' := fun x y => Subtype.ext (A.symm.map_add x y)
      map_smul' := fun c x => Subtype.ext (A.symm.map_smul c x) }
  exact LinearEquiv.ofLinear f g
    (by apply LinearMap.ext; intro x; apply Subtype.ext; exact A.apply_symm_apply x)
    (by apply LinearMap.ext; intro x; apply Subtype.ext; exact A.symm_apply_apply x)

theorem pointSplittingGroundKernel_equivOfSourceSquare_coe
    {E U V W Z : Type u} [Field E]
    [AddCommGroup U] [Module E U] [AddCommGroup V] [Module E V]
    [AddCommGroup W] [Module E W] [AddCommGroup Z] [Module E Z]
    (R : U →ₗ[E] V) (T : W →ₗ[E] Z)
    (A : U ≃ₗ[E] W) (B : V ≃ₗ[E] Z)
    (h : B.toLinearMap.comp (R.comp A.symm.toLinearMap) = T) (x : R.ker) :
    (pointSplittingGroundKernel_equivOfSourceSquare R T A B h x : W) = A x := rfl

end PfaffianDescent
