; ModuleID = 'add.c'
source_filename = "add.c"
target datalayout = "e-m:e-p:64:64-i64:64-i128:128-n64-S128"
target triple = "riscv64-unknown-unknown"

@c = dso_local local_unnamed_addr global [1024 x i64] zeroinitializer, align 8
@b = dso_local local_unnamed_addr global [1024 x i64] zeroinitializer, align 8
@a = dso_local local_unnamed_addr global [1024 x i64] zeroinitializer, align 8
@f = dso_local local_unnamed_addr global [1024 x i32] zeroinitializer, align 4
@e = dso_local local_unnamed_addr global [1024 x i32] zeroinitializer, align 4
@d = dso_local local_unnamed_addr global [1024 x i32] zeroinitializer, align 4
@.str = private unnamed_addr constant [5 x i8] c"%ld\0A\00", align 1
@.str.1 = private unnamed_addr constant [4 x i8] c"%d\0A\00", align 1

; Function Attrs: noinline nounwind
define dso_local signext i32 @main() local_unnamed_addr #0 {
  %1 = tail call signext i32 @rand() #3
  %2 = srem i32 %1, 1024
  %3 = sext i32 %2 to i64
  %4 = getelementptr inbounds [1024 x i64], [1024 x i64]* @c, i64 0, i64 %3
  %5 = load i64, i64* %4, align 8, !tbaa !4
  %6 = add i64 %5, 31
  store i64 %6, i64* %4, align 8, !tbaa !4
  %7 = getelementptr inbounds [1024 x i64], [1024 x i64]* @b, i64 0, i64 %3
  %8 = load i64, i64* %7, align 8, !tbaa !4
  %9 = add nsw i64 %8, -51
  store i64 %9, i64* %7, align 8, !tbaa !4
  %10 = add i64 %9, %6
  %11 = getelementptr inbounds [1024 x i64], [1024 x i64]* @a, i64 0, i64 %3
  store i64 %10, i64* %11, align 8, !tbaa !4
  %12 = getelementptr inbounds [1024 x i32], [1024 x i32]* @f, i64 0, i64 %3
  %13 = load i32, i32* %12, align 4, !tbaa !8
  %14 = add i32 %13, 31
  store i32 %14, i32* %12, align 4, !tbaa !8
  %15 = getelementptr inbounds [1024 x i32], [1024 x i32]* @e, i64 0, i64 %3
  %16 = load i32, i32* %15, align 4, !tbaa !8
  %17 = add nsw i32 %16, -51
  store i32 %17, i32* %15, align 4, !tbaa !8
  %18 = add i32 %17, %14
  %19 = getelementptr inbounds [1024 x i32], [1024 x i32]* @d, i64 0, i64 %3
  store i32 %18, i32* %19, align 4, !tbaa !8
  %20 = tail call signext i32 (i8*, ...) @printf(i8* nonnull dereferenceable(1) getelementptr inbounds ([5 x i8], [5 x i8]* @.str, i64 0, i64 0), i64 %10)
  %21 = load i32, i32* %19, align 4, !tbaa !8
  %22 = tail call signext i32 (i8*, ...) @printf(i8* nonnull dereferenceable(1) getelementptr inbounds ([4 x i8], [4 x i8]* @.str.1, i64 0, i64 0), i32 signext %21)
  ret i32 0
}

; Function Attrs: nounwind
declare dso_local signext i32 @rand() local_unnamed_addr #1

; Function Attrs: nofree nounwind
declare dso_local noundef signext i32 @printf(i8* nocapture noundef readonly, ...) local_unnamed_addr #2

attributes #0 = { noinline nounwind "frame-pointer"="none" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-features"="+64bit,+a,+d,+f,+m,+relax,-save-restore" }
attributes #1 = { nounwind "frame-pointer"="none" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-features"="+64bit,+a,+d,+f,+m,+relax,-save-restore" }
attributes #2 = { nofree nounwind "frame-pointer"="none" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-features"="+64bit,+a,+d,+f,+m,+relax,-save-restore" }
attributes #3 = { nounwind }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 1, !"target-abi", !"lp64d"}
!2 = !{i32 1, !"SmallDataLimit", i32 8}
!3 = !{!"clang version 13.0.1 (https://github.com/llvm/llvm-project.git 75e33f71c2dae584b13a7d1186ae0a038ba98838)"}
!4 = !{!5, !5, i64 0}
!5 = !{!"long", !6, i64 0}
!6 = !{!"omnipotent char", !7, i64 0}
!7 = !{!"Simple C/C++ TBAA"}
!8 = !{!9, !9, i64 0}
!9 = !{!"int", !6, i64 0}
