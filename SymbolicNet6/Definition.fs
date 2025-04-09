namespace MathNet.Symbolics

open MathNet.Numerics.LinearAlgebra
open System.Collections.Concurrent
module Definition =
    type Cur = decimal //==> evaluate 用 dict 送進去的

    type DefBody =
    | DBExp of Expression []
    | DBFun of (ConcurrentDictionary<string, FloatingPoint> (*前一輸出*) -> FloatingPoint list -> ConcurrentDictionary<string, FloatingPoint> (*本次輸出*) )

    type DefType =
    | DTExp of (Symbol list) * Expression //用表達式表示函數 body，symbol 是表達式中參數名
    //| DTExpSys of (Symbol list) * Expression * (Symbol list) //用表達式表示函數 body，symbol 是表達式中參數名，最後是系統變數(例如當根位置, context 等等)
    | DTProc of ((Symbol list) * DefBody * (Symbol list)) list //(_, _, s) list 最後的 s 是系統變數(例如當根位置, context 等等)
    | DTFunAction of (unit -> unit)
    | DTFunI1toI1 of (int -> int)
    | DTFunF2toV1 of (float -> float -> Vector<float>)
    | DTCurF2toV1 of (Cur -> float -> float -> Vector<float>) * Symbol
    | DTCurF3toV1 of (Cur -> float -> float -> float -> Vector<float>) * Symbol // cur 以 decimal 表示當根位置，然後傳入的參數是 float * float * float
    | KeyWord

    let mutable funDict = new System.Collections.Concurrent.ConcurrentDictionary<string, DefType>()

    let kwlist = [ "vec", true; "mat_by_row", true; "mat_by_col", true; "mat_multiply", true;
                   "htensor", true; 
                   "gtensor", true;
                   "list_of", true; "lo", true;
                   //"htensor", true
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
