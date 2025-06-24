rule empty_if {
    bool x;
    if (x) {} else {}
    assert true;
}
