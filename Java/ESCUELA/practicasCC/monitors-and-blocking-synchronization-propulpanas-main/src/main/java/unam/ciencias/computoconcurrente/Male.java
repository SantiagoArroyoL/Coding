package unam.ciencias.computoconcurrente;

public class Male extends Participant {

  public Male(Toilette toilette) {
    super(toilette);
  }

  @Override
  public void enterToilette() throws InterruptedException {
    this.toilette.enterMale();
  }

  @Override
  public void leaveToilette() {
    this.toilette.leaveMale();
  }
}
