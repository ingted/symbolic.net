namespace MathNet.Symbolics

open MathNet.Numerics.LinearAlgebra
open System.Collections.Concurrent
open System.Collections.Generic

module Definition =
    let mutable funDict = new FunDict()

    let kwlist = [ "vec", true; "mat_by_row", true; "mat_by_col", true; "mat_multiply", true;
                   "htensor", true; 
                   "gtensor", true;
                   "list_of", true; "lo", true;
                   //"htensor", true
                   "str"    , true
                   "expr"   , true
                   "param"  , true
                   ]

    let keyWord = dict kwlist

    kwlist |> List.iter (fun (k, _) -> funDict.TryAdd(k, KeyWord) |> ignore)

    let defineSafe fnm exp =
        if keyWord.ContainsKey fnm then
            failwith "used function name"
        funDict.TryAdd (fnm, DTExp exp)

    let define fnm exp =
        if keyWord.ContainsKey fnm then
            failwith "used function name"
        funDict.AddOrUpdate(
            fnm
            , (fun nm -> DTExp exp)
            , (fun nm cur_exp -> DTExp exp)
        )

    let defProc fnm l =
        if keyWord.ContainsKey fnm then
            failwith "used function name"
        funDict.AddOrUpdate(
            fnm
            , (fun nm -> DTProc l)
            , (fun nm cur_exp -> DTProc l)
        )


    let defAct fnm f =
        if keyWord.ContainsKey fnm then
            failwith "used function name"
        funDict.AddOrUpdate(
            fnm
            , (fun nm -> DTFunAction f)
            , (fun nm cur_exp -> DTFunAction f)
        )

    let def1ito1i fnm f =
        if keyWord.ContainsKey fnm then
            failwith "used function name"
        funDict.AddOrUpdate(
            fnm
            , (fun nm -> DTFunI1toI1 f)
            , (fun nm cur_exp -> DTFunI1toI1 f)
        )


    let def2fto1v fnm f =
        if keyWord.ContainsKey fnm then
            failwith "used function name"
        funDict.AddOrUpdate(
            fnm
            , (fun nm -> DTFunF2toV1 f)
            , (fun nm cur_exp -> DTFunF2toV1 f)
        )

    let cur2fto1v fnm f =
        if keyWord.ContainsKey fnm then
            failwith "used function name"
        funDict.AddOrUpdate(
            fnm
            , (fun nm -> DTCurF2toV1 f)
            , (fun nm cur_exp -> DTCurF2toV1 f)
        )

    let cur3fto1v fnm f =
        if keyWord.ContainsKey fnm then
            failwith "used function name"
        funDict.AddOrUpdate(
            fnm
            , (fun nm -> DTCurF3toV1 f)
            , (fun nm cur_exp -> DTCurF3toV1 f)
        )
