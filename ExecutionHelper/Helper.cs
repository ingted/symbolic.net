using System;
using System.Collections.Generic;
using System.Text;
using System.Linq.Expressions;


namespace ExecutionHelper
{
    public static class Helper
    {
        public static Delegate compileIt(LambdaExpression le)
        {
            return le.Compile();
        }

        public static object executeIt(Delegate del, object[] param)
        {
            return del.DynamicInvoke(param);
        }
    }
}
