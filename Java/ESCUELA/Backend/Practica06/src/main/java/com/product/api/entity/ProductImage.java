package com.product.api.entity;

import javax.persistence.Id;
import javax.persistence.Table;
import javax.persistence.Column;
import javax.persistence.Entity;
import javax.persistence.GeneratedValue;
import javax.persistence.GenerationType;
import javax.validation.constraints.Max;
import javax.validation.constraints.Min;
import javax.validation.constraints.NotNull;

import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonProperty;

@Entity
@Table(name = "product_image")
public class ProductImage {

    @Id
    @GeneratedValue(strategy = GenerationType.IDENTITY)
    @JsonProperty("product_image_id")
    @Column(name = "product_image_id")
    private Integer product_image_id;

    @NotNull(message = "product_id is required")
    @Column(name = "product_id")
    @JsonProperty("product_id")
    private Integer product_id;

    @NotNull(message = "image is required")
    @Column(name = "image")
    @JsonProperty("image")
    private String image;

    @Column(name = "status")
    @Min(value = 0, message = "status must be 0 or 1")
    @Max(value = 1, message = "satus must be 0 or 1")
    @JsonIgnore
    private int status;

    public Integer getProduct_image_id() {
        return this.product_image_id;
    }

    public void setProduct_image_id(Integer product_image_id) {
        this.product_image_id = product_image_id;
    }

    public Integer getProduct_id() {
        return this.product_id;
    }

    public void setProduct_id(Integer product_id) {
        this.product_id = product_id;
    }

    public String getImage() {
        return this.image;
    }

    public void setImage(String image) {
        this.image = image;
    }

    public int getStatus() {
        return this.status;
    }

    public void setStatus(int status) {
        this.status = status;
    }

}
