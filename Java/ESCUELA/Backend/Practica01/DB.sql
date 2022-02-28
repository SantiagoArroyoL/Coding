CREATE DATABASE `backend` /*!40100 DEFAULT CHARACTER SET utf8 COLLATE utf8_unicode_ci */ /*!80016 DEFAULT ENCRYPTION='N' */;
CREATE TABLE `customers` (
  `customer_id` int NOT NULL,
  `name` varchar(45) COLLATE utf8_unicode_ci NOT NULL,
  `surname` varchar(45) COLLATE utf8_unicode_ci NOT NULL,
  `rfc` varchar(45) COLLATE utf8_unicode_ci NOT NULL,
  `mail` varchar(45) COLLATE utf8_unicode_ci NOT NULL,
  `region_id` int NOT NULL,
  PRIMARY KEY (`customer_id`),
  KEY `fk_regions_region_idx` (`region_id`),
  CONSTRAINT `fk_regions_region` FOREIGN KEY (`region_id`) REFERENCES `regions` (`region_id`) ON DELETE CASCADE ON UPDATE CASCADE
) ENGINE=InnoDB DEFAULT CHARSET=utf8mb3 COLLATE=utf8_unicode_ci;
CREATE TABLE `regions` (
  `region_id` int NOT NULL AUTO_INCREMENT,
  `region` varchar(45) COLLATE utf8_unicode_ci NOT NULL,
  PRIMARY KEY (`region_id`)
) ENGINE=InnoDB AUTO_INCREMENT=6 DEFAULT CHARSET=utf8mb3 COLLATE=utf8_unicode_ci;

