/*@ requires \valid(thatint);
  @*/
void assert_separated(int *thatint)
{
    int localint = 2;
    int *localmallocint = malloc(sizeof(int));

    // cannot be proved as you have no assumption on thatint
    //@ assert \separated(thatint, &localint);
    //@ assert \separated(thatint, localmallocint);
}
