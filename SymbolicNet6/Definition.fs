namespace MathNet.Symbolics

module Definition =

    type DefType =
    | DTExp of (Symbol list) * Expression //用表達式表示函數 body，symbol 是表達式中參數名
    | DTFunAction of (unit -> unit)
    | DTFunI1toI1 of (int -> int)
    | KeyWord

    let funDict = new System.Collections.Concurrent.ConcurrentDictionary<string, DefType>()

    let kwlist = [ "vec", true; "mat_by_row", true; "mat_by_col", true; "mat_multiply", true;
                   "htensor", true; 
                   "gtensor", true;
                   "list_of", true; "lo", true;
                   "htensor", true
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
