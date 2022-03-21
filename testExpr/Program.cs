using System;
using System.Linq;
using System.Linq.Expressions;
using NJection;
using NJection.LambdaConverter.Fluent;

namespace test
{
    public class TestMain
    {
        public static void Main(string[] args)
        {

            //Func<int, object> func = x => (object)x;
            var lambda = Lambda.TransformMethodTo<Func<int, object>>()
                           .From(() => func)
                           .ToLambda();

            

            Console.WriteLine("Hello, World!");
        }
        public static int Parse(string value)
        {
            return int.Parse(value);
        }

        public static object func(int value)
        {
            return (object)value;
        }
    }
}



