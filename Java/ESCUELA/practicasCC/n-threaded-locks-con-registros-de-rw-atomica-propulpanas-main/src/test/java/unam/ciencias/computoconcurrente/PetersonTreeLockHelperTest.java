package unam.ciencias.computoconcurrente;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.condition.EnabledIf;

@EnabledIf("testSuiteEnabled")
class PetersonTreeLockHelperTest {

  static boolean testSuiteEnabled() {
    return PropertiesLoader.getBooleanProperty("tree-lock-helpers.enabled");
  }

  @Test
  void getLockID() {
    assertEquals(0, PetersonTreeLockHelper.getLockID(8, 2, 0));
    assertEquals(1, PetersonTreeLockHelper.getLockID(8, 2, 1));

    assertEquals(0, PetersonTreeLockHelper.getLockID(8, 2, 2));
    assertEquals(1, PetersonTreeLockHelper.getLockID(8, 2, 3));

    assertEquals(0, PetersonTreeLockHelper.getLockID(8, 2, 4));
    assertEquals(1, PetersonTreeLockHelper.getLockID(8, 2, 5));

    assertEquals(0, PetersonTreeLockHelper.getLockID(8, 2, 6));
    assertEquals(1, PetersonTreeLockHelper.getLockID(8, 2, 7));

    assertEquals(0, PetersonTreeLockHelper.getLockID(8, 1, 0));
    assertEquals(0, PetersonTreeLockHelper.getLockID(8, 1, 1));

    assertEquals(1, PetersonTreeLockHelper.getLockID(8, 1, 2));
    assertEquals(1, PetersonTreeLockHelper.getLockID(8, 1, 3));

    assertEquals(0, PetersonTreeLockHelper.getLockID(8, 1, 4));
    assertEquals(0, PetersonTreeLockHelper.getLockID(8, 1, 5));

    assertEquals(1, PetersonTreeLockHelper.getLockID(8, 1, 6));
    assertEquals(1, PetersonTreeLockHelper.getLockID(8, 1, 7));

    assertEquals(0, PetersonTreeLockHelper.getLockID(8, 0, 0));
    assertEquals(0, PetersonTreeLockHelper.getLockID(8, 0, 1));

    assertEquals(0, PetersonTreeLockHelper.getLockID(8, 0, 2));
    assertEquals(0, PetersonTreeLockHelper.getLockID(8, 0, 3));

    assertEquals(1, PetersonTreeLockHelper.getLockID(8, 0, 4));
    assertEquals(1, PetersonTreeLockHelper.getLockID(8, 0, 5));

    assertEquals(1, PetersonTreeLockHelper.getLockID(8, 0, 6));
    assertEquals(1, PetersonTreeLockHelper.getLockID(8, 0, 7));
  }

  @Test
  void getLockIndex() {
    assertEquals(3, PetersonTreeLockHelper.getLockIndex(8, 2, 0));
    assertEquals(3, PetersonTreeLockHelper.getLockIndex(8, 2, 1));

    assertEquals(4, PetersonTreeLockHelper.getLockIndex(8, 2, 2));
    assertEquals(4, PetersonTreeLockHelper.getLockIndex(8, 2, 3));

    assertEquals(5, PetersonTreeLockHelper.getLockIndex(8, 2, 4));
    assertEquals(5, PetersonTreeLockHelper.getLockIndex(8, 2, 5));

    assertEquals(6, PetersonTreeLockHelper.getLockIndex(8, 2, 6));
    assertEquals(6, PetersonTreeLockHelper.getLockIndex(8, 2, 7));

    assertEquals(1, PetersonTreeLockHelper.getLockIndex(8, 1, 0));
    assertEquals(1, PetersonTreeLockHelper.getLockIndex(8, 1, 1));

    assertEquals(1, PetersonTreeLockHelper.getLockIndex(8, 1, 2));
    assertEquals(1, PetersonTreeLockHelper.getLockIndex(8, 1, 3));

    assertEquals(2, PetersonTreeLockHelper.getLockIndex(8, 1, 4));
    assertEquals(2, PetersonTreeLockHelper.getLockIndex(8, 1, 5));

    assertEquals(2, PetersonTreeLockHelper.getLockIndex(8, 1, 6));
    assertEquals(2, PetersonTreeLockHelper.getLockIndex(8, 1, 7));

    assertEquals(0, PetersonTreeLockHelper.getLockIndex(8, 0, 0));
    assertEquals(0, PetersonTreeLockHelper.getLockIndex(8, 0, 1));

    assertEquals(0, PetersonTreeLockHelper.getLockIndex(8, 0, 2));
    assertEquals(0, PetersonTreeLockHelper.getLockIndex(8, 0, 3));

    assertEquals(0, PetersonTreeLockHelper.getLockIndex(8, 0, 4));
    assertEquals(0, PetersonTreeLockHelper.getLockIndex(8, 0, 5));

    assertEquals(0, PetersonTreeLockHelper.getLockIndex(8, 0, 6));
    assertEquals(0, PetersonTreeLockHelper.getLockIndex(8, 0, 7));
  }
}
