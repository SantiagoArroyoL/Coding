package unam.ciencias.computoconcurrente;

import org.junit.jupiter.api.condition.DisabledIf;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

@Target(ElementType.METHOD)
@Retention(RetentionPolicy.RUNTIME)
@DisabledIf("hasFewerThanEightCores")
public @interface DisableIfHasFewerThanEightCores {}
