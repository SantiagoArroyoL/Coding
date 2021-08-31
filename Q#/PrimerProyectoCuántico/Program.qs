namespace PrimerProyectoCuantico {

    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Measurment;
    
    //@EntryPoint()
    //operation SayHello() : Unit {
    //    Message("Hello quantum world!");
    //}

    @EntryPoint()
    operation GenerateQubit() : Result {
        using(q = Qubit()){
            H(q); //Mide q

            return MResetZ(q);
        }
    }
}
