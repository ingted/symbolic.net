module TestCore
#if INTERACTIVE
#r "nuget: Unquote, 7.0.0"
#endif

open Microsoft.FSharp.Quotations.Patterns
open Swensen.Unquote
open Swensen
open Microsoft.FSharp.Quotations
open System.Collections.Generic

let q2str (q:Expr) =
    (Operators.unquote q).DecompiledReductions.[0]
    

let testBody f = (q2str f).Substring(10)

let mutable testIdFilter : int [] option = None
let mutable testIdFilterOut : int [] option = None

let inline test<'T when 'T: equality> i ifForcePrint (f: Expr<unit -> 'T>) (subject:'T)  =
    if (testIdFilter.IsNone || testIdFilter.Value |> Array.contains i) &&  not (testIdFilterOut.IsSome && (testIdFilterOut.Value |> Array.contains i)) then
        try
            let o = (Operators.eval f) ()
            let diff = o = subject
            if not diff || ifForcePrint % 2 = 0 then
                printfn "[%s][%b] %s %A == %A" (i.ToString().PadLeft(3, ' ')) diff (if ifForcePrint % 3 = 0 then testBody f + " | " else "") o subject
            diff, f.Raw
        with
        | exn ->
            let diff = exn.InnerException.Message = subject.ToString()
            if not diff ||  ifForcePrint % 2 = 0 then
                printfn "[%s][%b] %s | %s == %A" (i.ToString().PadLeft(3, ' ')) diff (testBody f) exn.InnerException.Message subject
            diff, f.Raw
        |> Some
    else
        None


