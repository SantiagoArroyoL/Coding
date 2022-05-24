package com.product.exception;

import java.time.LocalDateTime;

import com.fasterxml.jackson.annotation.JsonFormat;

import org.springframework.http.HttpStatus;

public class ExceptionResponse {
    
    @JsonFormat(shape = JsonFormat.Shape.STRING, pattern="yyyy-MM-dd hh-mm-ss")
    private LocalDateTime timestamp;
    private Integer status;
    private HttpStatus error;
    private String message;
    private String path;

    public ExceptionResponse() {

    }

    public LocalDateTime getTimestamp() {
        return this.timestamp;
    }

    public void setTimestamp(LocalDateTime timestamp) {
        this.timestamp = timestamp;
    }

    public Integer getStatus() {
        return this.status;
    }

    public void setStatus(Integer status) {
        this.status = status;
    }

    public HttpStatus getError() {
        return this.error;
    }

    public void setError(HttpStatus error) {
        this.error = error;
    }

    public String getMessage() {
        return this.message;
    }

    public void setMessage(String message) {
        this.message = message;
    }

    public String getPath() {
        return this.path;
    }

    public void setPath(String path) {
        this.path = path;
    }

}
