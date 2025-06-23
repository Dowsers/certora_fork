methods {
    function _.digestNonce(uint) external => 4 expect uint;
}

rule easy(uint arb) {
    env e;
    assert getSigner(e, arb) == 4;
}