// Lean compiler output
// Module: PureLean.LogicFunctions
// Imports: public import Init public meta import Init
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_LogicFunctions_Section01_optMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_LogicFunctions_Section01_optMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_LogicFunctions_Section01_optBind___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_LogicFunctions_Section01_optBind(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_LogicFunctions_Section02_iterFn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_LogicFunctions_Section02_iterFn___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_LogicFunctions_Section02_iterFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_LogicFunctions_Section02_iterFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_purelean_PureLean_LogicFunctions_Section01_optMap___redArg(lean_object* v_f_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v___x_3_; 
lean_dec(v_f_1_);
v___x_3_ = lean_box(0);
return v___x_3_;
}
else
{
lean_object* v_val_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_12_; 
v_val_4_ = lean_ctor_get(v_x_2_, 0);
v_isSharedCheck_12_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_12_ == 0)
{
v___x_6_ = v_x_2_;
v_isShared_7_ = v_isSharedCheck_12_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_val_4_);
lean_dec(v_x_2_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_12_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
lean_object* v___x_8_; lean_object* v___x_10_; 
v___x_8_ = lean_apply_1(v_f_1_, v_val_4_);
if (v_isShared_7_ == 0)
{
lean_ctor_set(v___x_6_, 0, v___x_8_);
v___x_10_ = v___x_6_;
goto v_reusejp_9_;
}
else
{
lean_object* v_reuseFailAlloc_11_; 
v_reuseFailAlloc_11_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_11_, 0, v___x_8_);
v___x_10_ = v_reuseFailAlloc_11_;
goto v_reusejp_9_;
}
v_reusejp_9_:
{
return v___x_10_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_LogicFunctions_Section01_optMap(lean_object* v_00_u03b1_13_, lean_object* v_00_u03b2_14_, lean_object* v_f_15_, lean_object* v_x_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lp_purelean_PureLean_LogicFunctions_Section01_optMap___redArg(v_f_15_, v_x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_LogicFunctions_Section01_optBind___redArg(lean_object* v_x_18_, lean_object* v_x_19_){
_start:
{
if (lean_obj_tag(v_x_18_) == 0)
{
lean_object* v___x_20_; 
lean_dec_ref(v_x_19_);
v___x_20_ = lean_box(0);
return v___x_20_;
}
else
{
lean_object* v_val_21_; lean_object* v___x_22_; 
v_val_21_ = lean_ctor_get(v_x_18_, 0);
lean_inc(v_val_21_);
lean_dec_ref_known(v_x_18_, 1);
v___x_22_ = lean_apply_1(v_x_19_, v_val_21_);
return v___x_22_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_LogicFunctions_Section01_optBind(lean_object* v_00_u03b1_23_, lean_object* v_00_u03b2_24_, lean_object* v_x_25_, lean_object* v_x_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lp_purelean_PureLean_LogicFunctions_Section01_optBind___redArg(v_x_25_, v_x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_LogicFunctions_Section02_iterFn___redArg(lean_object* v_f_28_, lean_object* v_x_29_, lean_object* v_x_30_){
_start:
{
lean_object* v_zero_31_; uint8_t v_isZero_32_; 
v_zero_31_ = lean_unsigned_to_nat(0u);
v_isZero_32_ = lean_nat_dec_eq(v_x_29_, v_zero_31_);
if (v_isZero_32_ == 1)
{
lean_dec(v_f_28_);
lean_inc(v_x_30_);
return v_x_30_;
}
else
{
lean_object* v_one_33_; lean_object* v_n_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_one_33_ = lean_unsigned_to_nat(1u);
v_n_34_ = lean_nat_sub(v_x_29_, v_one_33_);
lean_inc(v_f_28_);
v___x_35_ = lp_purelean_PureLean_LogicFunctions_Section02_iterFn___redArg(v_f_28_, v_n_34_, v_x_30_);
lean_dec(v_n_34_);
v___x_36_ = lean_apply_1(v_f_28_, v___x_35_);
return v___x_36_;
}
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_LogicFunctions_Section02_iterFn___redArg___boxed(lean_object* v_f_37_, lean_object* v_x_38_, lean_object* v_x_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = lp_purelean_PureLean_LogicFunctions_Section02_iterFn___redArg(v_f_37_, v_x_38_, v_x_39_);
lean_dec(v_x_39_);
lean_dec(v_x_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_LogicFunctions_Section02_iterFn(lean_object* v_00_u03b1_41_, lean_object* v_f_42_, lean_object* v_x_43_, lean_object* v_x_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lp_purelean_PureLean_LogicFunctions_Section02_iterFn___redArg(v_f_42_, v_x_43_, v_x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_purelean_PureLean_LogicFunctions_Section02_iterFn___boxed(lean_object* v_00_u03b1_46_, lean_object* v_f_47_, lean_object* v_x_48_, lean_object* v_x_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = lp_purelean_PureLean_LogicFunctions_Section02_iterFn(v_00_u03b1_46_, v_f_47_, v_x_48_, v_x_49_);
lean_dec(v_x_49_);
lean_dec(v_x_48_);
return v_res_50_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_purelean_PureLean_LogicFunctions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize_runtime_module();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
